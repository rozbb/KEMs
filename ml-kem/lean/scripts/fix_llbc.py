"""Post-process a monomorphized Charon LLBC file so that Aeneas accepts it.

Usage: fix_llbc.py MONO.llbc GENERIC.llbc OUT.llbc

ml-kem is generic over its parameter sets via typenum, which Charon and Aeneas can't handle
generically, so we extract it with `charon --monomorphize`. Aeneas doesn't officially support
monomorphized crates, and trips over a handful of artifacts of monomorphization. This script fixes
those up. A few passes need generic declarations of core items, which monomorphization drops; we
copy them from GENERIC.llbc, a small non-monomorphized extraction of the same crate. Both inputs
must be produced with `--no-dedup-serialized-ast`.

None of these passes change the meaning of the code: they only restore declarations, rename items,
or replace an operation by a call to a function with the same semantics.
"""
import json
import sys

mono_path, generic_path, out_path = sys.argv[1:4]
mono = json.load(open(mono_path))
m = mono['translated']
g = json.load(open(generic_path))['translated']

CORE_CRATES = ('core', 'alloc', 'std')


def path(name):
    """The identifiers of an item name, with `{impl}` for impl blocks."""
    return tuple(p['Ident'][0] if 'Ident' in p else '{impl}' for p in name if 'Instantiated' not in p)


def is_core(name):
    return 'Ident' in name[0] and name[0]['Ident'][0] in CORE_CRATES


def walk(o, f):
    """Rebuild a JSON value bottom-up, applying `f` to every dict."""
    if isinstance(o, dict):
        return f({k: walk(v, f) for k, v in o.items()})
    if isinstance(o, list):
        return [walk(v, f) for v in o]
    return o


def item_kinds():
    return (('Type', 'type_decls'), ('Fun', 'fun_decls'), ('Global', 'global_decls'),
            ('TraitDecl', 'trait_decls'), ('TraitImpl', 'trait_impls'))


def set_name(kind, i, name):
    m[dict(item_kinds())[kind]][i]['item_meta']['name'] = name
    for e in m['item_names']:
        if e['key'] == {kind: i}:
            e['value'] = name


def add_item(kind, decl):
    """Append a new declaration, returning its id."""
    table = m[dict(item_kinds())[kind]]
    decl['def_id'] = len(table)
    table.append(decl)
    m['item_names'].append({'key': {kind: decl['def_id']}, 'value': decl['item_meta']['name']})
    return decl['def_id']


# Copying declarations from the generic file means remapping the ids they mention.
mono_files = {json.dumps(f['name']): f['id'] for f in m['files']}
gen_file_ids = {}
for f in g['files']:
    key = json.dumps(f['name'])
    if key not in mono_files:
        mono_files[key] = len(m['files'])
        m['files'].append(dict(f, id=mono_files[key]))
    gen_file_ids[f['id']] = mono_files[key]
mono_trait_ids = {path(t['item_meta']['name']): i for i, t in enumerate(m['trait_decls']) if t}
for e in m['item_names']:
    if 'TraitDecl' in e['key']:
        mono_trait_ids.setdefault(path(e['value']), e['key']['TraitDecl'])
gen_trait_ids = {i: mono_trait_ids.get(path(t['item_meta']['name']))
                 for i, t in enumerate(g['trait_decls']) if t}


gen_type_ids = {}


def from_generic(decl):
    def f(o):
        if isinstance(o.get('file_id'), int):
            o['file_id'] = gen_file_ids[o['file_id']]
        if set(o) == {'id', 'generics', 'builtin'} and o['builtin'] is None:
            assert o['id'] in gen_type_ids, f'type {o["id"]} of the generic file is not available'
            o['id'] = gen_type_ids[o['id']]
        return o
    return walk(decl, f)


def remap_trait_ref(o):
    """Remap a reference to a trait declaration (`{skip_binder: {id, generics}}`) in a copied item."""
    if isinstance(o.get('skip_binder'), dict) and set(o['skip_binder']) == {'id', 'generics'}:
        tid = gen_trait_ids[o['skip_binder']['id']]
        assert tid is not None, o
        return dict(o, skip_binder=dict(o['skip_binder'], id=tid))
    return o


# 1. Monomorphized instances of core builtin types (`Option::<usize>`, `Range::<usize>`, ...) are
# separate type declarations, which Aeneas doesn't recognize as its builtins. We copy the generic
# declarations here, and replace the monomorphized ones by them (applied to the instantiation's type arguments.
BUILTIN_TYPES = {('core', 'option', 'Option'), ('core', 'result', 'Result'),
                 ('core', 'ops', 'range', 'Range'), ('core', 'ops', 'range', 'RangeTo'),
                 ('core', 'ops', 'range', 'RangeFrom')}
generic_type_ids = {}
copied_types = [t for t in g['type_decls'] if t is not None and path(t['item_meta']['name']) in BUILTIN_TYPES]
for k, t in enumerate(copied_types):
    gen_type_ids[t['def_id']] = len(m['type_decls']) + k
for t in copied_types:
    generic_type_ids[path(t['item_meta']['name'])] = add_item('Type', from_generic(t))


# 2. Charon replaces some operations by calls to generic builtins (`[T; N]::as_slice`,
# `core::array::repeat`, the array/slice `Index` impls, ...). Monomorphization drops their
# declarations, but Aeneas needs them to map the calls to its own Lean builtins (by name). The ids
# of these declarations are the same in both files, since Charon registers them first.
transplanted_funs = set()
for i, decl in enumerate(m['fun_decls']):
    if decl is None and i < len(g['fun_decls']) and g['fun_decls'][i] is not None:
        gen_name = path(g['fun_decls'][i]['item_meta']['name'])
        mono_name = next(path(e['value']) for e in m['item_names'] if e['key'] == {'Fun': i})
        assert gen_name == mono_name, (gen_name, mono_name)
        d = walk(from_generic(g['fun_decls'][i]), remap_trait_ref)
        m['fun_decls'][i] = d
        m['ordered_decls'].insert(0, {'Fun': {'NonRec': i}})
        transplanted_funs.add(i)


mono_builtin_types = {}
for i, t in enumerate(m['type_decls']):
    name = t['item_meta']['name'] if t else None
    if t is not None and path(name) in generic_type_ids and 'Instantiated' in name[-1]:
        mono_builtin_types[i] = (generic_type_ids[path(name)], name[-1]['Instantiated']['skip_binder'])


def use_generic_type(o):
    if set(o) == {'id', 'generics', 'builtin'} and o['id'] in mono_builtin_types:
        gid, generics = mono_builtin_types[o['id']]
        return {'id': gid, 'generics': walk(generics, use_generic_type), 'builtin': None}
    return o


for _, table in item_kinds():
    m[table] = [walk(d, use_generic_type) if d else None for d in m[table]]
# (the second half of pass 1)
for i in mono_builtin_types:
    m['type_decls'][i] = None
m['ordered_decls'] = [{'Type': {'NonRec': i}} for i in generic_type_ids.values()] + [
    grp for grp in m['ordered_decls'] if grp.get('Type', {}).get('NonRec') not in mono_builtin_types]

# 3. The declarations of the traits behind those builtins (`Index`, `IndexMut`, `SliceIndex`) are
# dropped as well. Aeneas needs them to match the (kept) core impls against its builtin models.
BUILTIN_TRAITS = {('core', 'ops', 'index', 'Index'), ('core', 'ops', 'index', 'IndexMut'),
                  ('core', 'slice', 'index', 'SliceIndex')}
gen_traits = {path(t['item_meta']['name']): t for t in g['trait_decls'] if t}
missing_traits = {e['key']['TraitDecl']: path(e['value']) for e in m['item_names']
                  if 'TraitDecl' in e['key'] and m['trait_decls'][e['key']['TraitDecl']] is None}
for i, name in missing_traits.items():
    if name in BUILTIN_TRAITS:
        gen_trait_ids[gen_traits[name]['def_id']] = i
for i, name in missing_traits.items():
    if name in BUILTIN_TRAITS:
        # Methods mentioning types (e.g. `get`, returning `Option`) would need their type ids
        # remapped; nothing calls them, so we leave them out.
        t = dict(gen_traits[name], vtable=None)
        t['methods'] = [meth for meth in t['methods'] if '"Adt"' not in json.dumps(meth)]
        d = from_generic(t)
        d['def_id'] = i
        for meth in d['methods']:
            meth['kind'] = {'TraitMethod': [i, meth['kind']['TraitMethod'][1]]}
        d = walk(d, remap_trait_ref)
        m['trait_decls'][i] = d
        m['ordered_decls'].insert(0, {'TraitDecl': {'NonRec': i}})

# 4. After monomorphization, every call refers directly to the function it calls, and trait impls
# only group methods (and have no method lists, so Aeneas would emit empty, ill-typed instances). We
# drop the impls outside `core` (whose names Aeneas matches against its builtins), and name their
# methods as if they were inherent: `{impl Compress for Elem}::compress` becomes
# `Elem_Compress::compress`.
type_names = {i: t['item_meta']['name'] for i, t in enumerate(m['type_decls']) if t}
for e in m['item_names']:
    if 'Type' in e['key']:
        type_names.setdefault(e['key']['Type'], e['value'])


def typenum_value(ty):
    """The value of a typenum unsigned integer type, or None."""
    t = ty.get('Untagged', ty)
    if 'Adt' not in t or not isinstance(t['Adt']['id'], int):
        return None
    name = type_names[t['Adt']['id']]
    p = path(name)
    if p[0] != 'typenum':
        return None
    if p[-1] == 'UTerm':
        return 0
    if p[-1] in ('B0', 'B1'):
        return int(p[-1][1])
    if p[-1] == 'UInt' and 'Instantiated' in name[-1]:
        u, b = name[-1]['Instantiated']['skip_binder']['types']
        return 2 * typenum_value(u) + typenum_value(b)
    return None


def short_ty(ty):
    """A short, readable rendering of a type, used to build names."""
    t = ty.get('Untagged', ty)
    if 'Adt' in t:
        a = t['Adt']
        if a.get('builtin') == 'Tuple' or not isinstance(a['id'], int):
            return 'Tuple'
        v = typenum_value(ty)
        if v is not None:
            return f'U{v}'
        name = type_names[a['id']]
        base = path(name)[-1]
        if 'Instantiated' in name[-1]:
            return base + short_generics(name[-1]['Instantiated']['skip_binder'])
        return base + short_generics(a['generics'])
    if 'Scalar' in t:
        s = t['Scalar']
        return list(s['Integer'].values())[0].lower() if 'Integer' in s else list(s.values())[0].lower()
    if 'Array' in t:
        return 'Arr' + short_ty(t['Array'][0])
    if 'Slice' in t:
        return 'Slice' + short_ty(t['Slice'][0])
    if 'Ref' in t:
        return 'Ref' + short_ty(t['Ref'][1])
    return 'T'


def short_generics(gen):
    types = gen['types']
    # Render typenum's `UInt<U, B>` as its value rather than as `U` and `B`.
    if len(types) == 2 and typenum_value(types[1]) in (0, 1) and typenum_value(types[0]) is not None \
            and path(type_names[types[1].get('Untagged', types[1])['Adt']['id']])[-1] in ('B0', 'B1'):
        return f'_U{2 * typenum_value(types[0]) + typenum_value(types[1])}'
    consts = []
    for c in gen['const_generics']:
        c = c.get('Untagged', c)
        try:
            consts.append(c[0]['Integer']['Unsigned'][1])
        except (KeyError, TypeError, IndexError):
            consts.append('C')
    return ''.join('_' + short_ty(t) for t in types) + ''.join('_' + c for c in consts)


dropped_impls = {}
for i, impl in enumerate(m['trait_impls']):
    if impl is None or is_core(impl['item_meta']['name']):
        continue
    trait = next(path(e['value']) for e in m['item_names'] if e['key'] == {'TraitDecl': impl['impl_trait']['id']})
    self_ty, *args = impl['impl_trait']['generics']['types']
    dropped_impls[i] = short_ty(self_ty) + '_' + trait[-1] + ''.join('_' + short_ty(t) for t in args)
    m['trait_impls'][i] = None
m['ordered_decls'] = [grp for grp in m['ordered_decls']
                      if grp.get('TraitImpl', {}).get('NonRec') not in dropped_impls]


def inherent_name(o):
    if set(o) == {'Impl'} and isinstance(o['Impl'], dict) and o['Impl'].get('Trait') in dropped_impls:
        return {'Ident': [dropped_impls[o['Impl']['Trait']], 0]}
    return o


m['item_names'] = walk(m['item_names'], inherent_name)
for _, table in item_kinds():
    for d in m[table]:
        if d is not None:
            d['item_meta']['name'] = walk(d['item_meta']['name'], inherent_name)
            if isinstance(d.get('src'), dict) and d['src'].get('TraitImpl', {}).get('impl_ref', {}).get('id') \
                    in dropped_impls:
                d['src'] = 'Normal'

# 5. Monomorphization erases the impl-level lifetimes of impls on reference types (e.g.
# `impl Add<&Polynomial> for &Polynomial`), leaving erased regions in signatures, which Aeneas
# rejects. We give each one a fresh region parameter, and pass an erased region for it at every
# call site (where regions are erased anyway).
added_regions = {}
for i, f in enumerate(m['fun_decls']):
    if f is None or '"Erased"' not in json.dumps(f['signature']):
        continue
    regions = f['generics']['regions']
    before = len(regions)

    def fresh(o):
        if isinstance(o.get('Ref'), list) and o['Ref'][0] == 'Erased':
            regions.append({'index': len(regions), 'name': None, 'variance': 'Covariant', 'mutability': 'Unknown'})
            return {'Ref': [{'Var': {'Free': len(regions) - 1}}, o['Ref'][1], o['Ref'][2]]}
        return o
    f['signature'] = walk(f['signature'], fresh)
    added_regions[i] = len(regions) - before


def pad_regions(o):
    r = o.get('Regular')
    if isinstance(r, dict) and isinstance(r.get('kind'), dict) and r['kind'].get('Fun') in added_regions:
        r['generics']['regions'] = r['generics']['regions'] + ['Erased'] * added_regions[r['kind']['Fun']]
    return o


m['fun_decls'] = [walk(d, pad_regions) if d else None for d in m['fun_decls']]

# 6. Aeneas derives Lean names from item names but ignores the `Instantiated` suffix that
# monomorphization appends, so e.g. `compress::<U4>` and `compress::<U10>` clash, and a type whose
# name ends in `Instantiated` crashes it. Outside `core` we fold the instantiation into the last
# identifier: `compress::<U4>` becomes `compress_U4`. Types drop the `Instantiated` element;
# functions keep it, since Aeneas's name matcher uses it.
for kind, table in item_kinds():
    drop = kind == 'Type'
    for i, d in enumerate(m[table]):
        name = d['item_meta']['name'] if d else None
        if not name or is_core(name) or 'Instantiated' not in name[-1] or 'Ident' not in name[-2]:
            continue
        v = typenum_value({'Adt': {'id': i, 'generics': {}, 'builtin': None}}) if kind == 'Type' else None
        if v is not None:
            ident = f'U{v}'
        else:
            ident = name[-2]['Ident'][0] + short_generics(name[-1]['Instantiated']['skip_binder'])
        set_name(kind, i, name[:-2] + [{'Ident': [ident, name[-2]['Ident'][1]]}] + ([] if drop else [name[-1]]))

# 7. Aeneas drops the crate prefix of ml-kem's own items, so their Lean names start with the module
# name (e.g. `encapsulation_key.EncapsulationKey_MlKem512.new`). A local variable of the same name
# (like `encapsulation_key` in `EncapsulationKey::new`) would shadow it, so we rename such locals.
modules = set()
for e in m['item_names']:
    p = path(e['value'])
    modules.add(p[1] if p[0] == 'ml_kem' and len(p) > 1 else p[0])
for f in m['fun_decls']:
    if f is not None and isinstance(f.get('body'), dict):
        for local in f['body']['Structured']['locals']['locals']:
            if local['name'] in modules:
                local['name'] += '_'

# 8. Monomorphization leaves indexing into builtin arrays (`[T; N]`) as place projections, because
# the `Index` builtins Charon would call instead are generic. Aeneas only supports indexing through
# function calls, so we rewrite `a[i]` into a call to a monomorphic helper
# `aeneas_mono::array_index_<T>_<N>(&a, i)` (or `array_index_mut_...`), and use its result instead.
# These helpers are defined in Lean in terms of Aeneas's `Array.index_usize`/`Array.index_mut_usize`.
USIZE = {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'Usize'}}}}
UNIT = {'Untagged': {'Adt': {'id': 0, 'generics': {'regions': [], 'types': [], 'const_generics': [],
                                                    'trait_refs': []}, 'builtin': 'Tuple'}}}
opaque_fn = next(f for f in m['fun_decls'] if f is not None and f['body'] == 'Opaque')
index_helpers = {}


def index_helper(elem_ty, n, mut):
    key = (json.dumps(elem_ty), n, mut)
    if key not in index_helpers:
        kind = 'Mut' if mut else 'Shared'
        arr_ty = {'Untagged': {'Array': [elem_ty, {'Untagged': [{'Integer': {'Unsigned': ['Usize', str(n)]}}, USIZE]},
                                         None]}}
        d = json.loads(json.dumps(opaque_fn))
        d['item_meta']['name'] = [{'Ident': ['aeneas_mono', 0]},
                                  {'Ident': [f"array_index{'_mut' if mut else ''}_{short_ty(elem_ty)}_{n}", 0]}]
        d['generics'] = {'regions': [{'index': 0, 'name': None, 'variance': 'Covariant', 'mutability': 'Unknown'}],
                         'types': [], 'const_generics': [], 'trait_clauses': [], 'regions_outlive': [],
                         'types_outlive': [], 'trait_type_constraints': []}
        d['signature'] = {'is_unsafe': False, 'abi': 'Rust', 'is_variadic': False,
                          'inputs': [{'Untagged': {'Ref': [{'Var': {'Free': 0}}, arr_ty, kind]}}, USIZE],
                          'output': {'Untagged': {'Ref': [{'Var': {'Free': 0}}, elem_ty, kind]}}}
        d['src'] = 'Normal'
        i = add_item('Fun', d)
        m['ordered_decls'].insert(0, {'Fun': {'NonRec': i}})
        index_helpers[key] = i
    return index_helpers[key]


def lower_indexing(body):
    locals_ = body['locals']['locals']
    span = body['span']

    def new_local(ty):
        locals_.append({'index': len(locals_), 'name': None, 'span': span, 'ty': ty, 'drop_flag_for': None})
        return len(locals_) - 1

    def stmt(kind):
        return {'span': span, 'id': 0, 'kind': kind, 'comments_before': []}

    def lower(place, mut, pre):
        """Rewrite the array indexing in `place`, emitting the calls it needs into `pre`."""
        if not isinstance(place.get('kind'), dict) or 'Projection' not in place['kind']:
            return place
        base, elem = place['kind']['Projection']
        base = lower(base, mut, pre)
        base_ty = base['ty'].get('Untagged', base['ty'])
        if not (isinstance(elem, dict) and 'Index' in elem and 'Array' in base_ty):
            return {'kind': {'Projection': [base, elem]}, 'ty': place['ty']}
        elem_ty, n = base_ty['Array'][0], int(base_ty['Array'][1]['Untagged'][0]['Integer']['Unsigned'][1])
        kind = 'Mut' if mut else 'Shared'
        arr_ref = new_local({'Untagged': {'Ref': ['Erased', base['ty'], kind]}})
        elem_ref = new_local({'Untagged': {'Ref': ['Erased', elem_ty, kind]}})
        arr_ref_ty, elem_ref_ty = locals_[arr_ref]['ty'], locals_[elem_ref]['ty']
        call = {'func': {'Regular': {'kind': {'Fun': index_helper(elem_ty, n, mut)},
                                     'generics': {'regions': ['Erased'], 'types': [], 'const_generics': [],
                                                  'trait_refs': []}}},
                'args': [{'Move': {'kind': {'Local': arr_ref}, 'ty': arr_ref_ty}}, elem['Index']['offset']],
                'dest': {'kind': {'Local': elem_ref}, 'ty': elem_ref_ty}, 'safety': 'Inherit'}
        pre += [stmt({'StorageLive': arr_ref}), stmt({'StorageLive': elem_ref}),
                stmt({'Assign': [{'kind': {'Local': arr_ref}, 'ty': arr_ref_ty},
                                 {'Ref': {'place': base, 'kind': kind,
                                          'ptr_metadata': {'Const': {'Untagged': [{'Adt': [None, []]}, UNIT]}}}}]}),
                stmt({'Call': {'call': call, 'on_unwind': {'span': span, 'id': 0,
                                                           'statements': [stmt('UnwindResume')]}}})]
        return {'kind': {'Projection': [{'kind': {'Local': elem_ref}, 'ty': elem_ref_ty}, 'Deref']}, 'ty': place['ty']}

    def lower_operands(o, pre):
        def f(x):
            for k in ('Copy', 'Move'):
                if set(x) == {k} and isinstance(x[k], dict) and 'kind' in x[k]:
                    return {k: lower(x[k], False, pre)}
            return x
        return walk(o, f)

    def lower_block(block):
        out = []
        for st in block['statements']:
            k, pre = st['kind'], []
            if isinstance(k, dict) and 'Assign' in k:
                dst, rv = k['Assign']
                if isinstance(rv, dict) and 'Ref' in rv:
                    rv = {'Ref': dict(rv['Ref'], place=lower(rv['Ref']['place'], rv['Ref']['kind'] != 'Shared', pre))}
                else:
                    rv = lower_operands(rv, pre)
                st = dict(st, kind={'Assign': [lower(dst, True, pre), rv]})
            elif isinstance(k, dict) and 'Call' in k:
                c = k['Call']['call']
                c = dict(c, args=[lower_operands(a, pre) for a in c['args']], dest=lower(c['dest'], True, pre))
                st = dict(st, kind={'Call': dict(k['Call'], call=c)})
            else:
                lower_nested(k)
            out += pre + [st]
        block['statements'] = out

    def lower_nested(o):
        if isinstance(o, dict):
            if isinstance(o.get('statements'), list):
                lower_block(o)
            else:
                for v in o.values():
                    lower_nested(v)
        elif isinstance(o, list):
            for v in o:
                lower_nested(v)

    lower_block(body['body'])


for f in m['fun_decls']:
    if f is not None and isinstance(f.get('body'), dict) and '"Index": {"offset"' in json.dumps(f['body']):
        lower_indexing(f['body']['Structured'])

# Aeneas checks that the crate was extracted with `--preset=aeneas`, which we did.
assert m['options']['preset'] == 'Aeneas'
json.dump(mono, open(out_path, 'w'))
print(f'fix_llbc: dropped {len(dropped_impls)} trait impls, added regions to {len(added_regions)} signatures, '
      f'added {len(index_helpers)} indexing helpers', file=sys.stderr)
