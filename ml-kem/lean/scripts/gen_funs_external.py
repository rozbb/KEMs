"""Generate `ExtractedRust/FunsExternal.lean` from `ExtractedRust/FunsExternal_Template.lean`.

Usage: gen_funs_external.py TEMPLATE TYPES OUTPUT

Aeneas declares every function it doesn't extract (from `core`, `hybrid-array`, `sha3`, ...) as an
axiom in the template. Because we extract a monomorphized crate, there is one copy of each such
function per instantiation, e.g. one `Array::concat` per pair of array sizes. Rather than writing
these models out by hand, this script recognizes each declaration by its name and emits a definition
for it. Unrecognized declarations are an error, so that new external functions get a model.

The models are part of our trusted base: they claim that each external function behaves like its
Lean definition. They are either one-liners in terms of Aeneas's own models of `core`, or (for the
hash functions) in terms of the SHA-3 spec. See `TrustBase.lean`.
"""
import re
import sys

template_path, types_path, out_path = sys.argv[1:4]
text = open(template_path).read()

# Type aliases from `Types.lean` (Aeneas erases single-field wrappers, e.g. hybrid-array's `Array`).
aliases = {}
for m in re.finditer(r'\ndef ([\w.]+) :=\s*([^\n]+(?:\n  [^\n]+)*)', open(types_path).read()):
    aliases[m.group(1)] = re.sub(r'\s+', ' ', m.group(2)).strip()


def default_value(ty):
    """The Lean value of `Default::default()` for the (alias of an) array or integer type `ty`."""
    ty = ty.strip()
    if ty.startswith('(') and ty.endswith(')'):
        return default_value(ty[1:-1])
    m = re.fullmatch(r'Std\.(U\d+|Usize)', ty)
    if m:
        return f'0#{m.group(1).lower()}'
    m = re.fullmatch(r'Array (\S+) (\d+)#usize', ty)
    if m:
        return f'(Array.repeat {m.group(2)}#usize {default_value(m.group(1))})'
    if ty in aliases:
        return default_value(aliases[ty])
    raise SystemExit(f'gen_funs_external.py: no default value for `{ty}`')

# Each declaration is a block: doc comment, attribute, `axiom NAME : TYPE`.
decls = []
for block in re.split(r'\n\s*\n', text):
    m = re.search(r'(?:^|\n)axiom\s+(\S+)\s*:\s*([\s\S]*)$', block)
    if m:
        doc = re.search(r'/--[\s\S]*?-/', block)
        attr = re.search(r'@\[rust_fun[\s\S]*?\](?=\s*\naxiom)', block)
        decls.append((m.group(1), re.sub(r'\s+', ' ', m.group(2)).strip(),
                      doc.group(0) if doc else '', attr.group(0) if attr else ''))


def array_size(ty):
    """The size of a (possibly aliased) byte array type, e.g. `hybrid_array.Array_u8_U32` -> 32."""
    m = re.search(r'Array_u8_U(\d+)\b', ty) or re.search(r'Array Std\.U8 (\d+)#usize', ty)
    assert m, ty
    return int(m.group(1))


def model(name, ty):
    """The Lean body (a `fun`) modelling external function `name` of type `ty`."""
    res = ty.split('→')[-1].strip()

    # Indexing into builtin arrays, see `fix_llbc.py`.
    if name.startswith('aeneas_mono.array_index_mut_'):
        return 'fun a i => Array.index_mut_usize a i'
    if name.startswith('aeneas_mono.array_index_'):
        return 'fun a i => Array.index_usize a i'

    # Integer operations, through `core` traits/inherent methods.
    if re.fullmatch(r'U\d+\.Insts\.CoreConvertIntoU(\d+)\.into', name):
        width = re.fullmatch(r'U\d+\.Insts\.CoreConvertIntoU(\d+)\.into', name).group(1)
        return f'fun x => ok (UScalar.cast .U{width} x)'
    if re.fullmatch(r'U\d+\.Insts\.CoreOpsArithAddU\d+\.add', name):
        return 'fun x y => x + y'
    if re.fullmatch(r'U\d+\.Insts\.CoreOpsArithSubU\d+\.sub', name):
        return 'fun x y => x - y'
    if re.fullmatch(r'U\d+\.Insts\.CoreOpsArithMulU\d+\.mul', name):
        return 'fun x y => x * y'
    if re.fullmatch(r'U\d+\.Insts\.CoreOpsBitBitAndU\d+\.bitand', name):
        return 'fun x y => ok (x &&& y)'
    if re.fullmatch(r'U\d+\.Insts\.CoreOpsBitShlUsize\.shl', name):
        return 'fun x s => x <<< s'
    if name == 'num_traits.identities.u16_One.one':
        return 'ok 1#u16'
    if name == 'core.num.U16.wrapping_neg':
        return 'fun x => ok ⟨-x.bv⟩'
    if name == 'core.num.U16.ilog2':
        return 'fun x => if x.val = 0 then fail .panic else ok ⟨BitVec.ofNat 32 (Nat.log2 x.val)⟩'
    if name == 'core.num.Usize.count_ones':
        return 'fun x => ok ⟨BitVec.ofNat 32 (Model.popcount x.val)⟩'

    # typenum constants
    m = re.fullmatch(r'typenum\.uint\.U(\d+)_Unsigned\.(USIZE|U8)_\w+', name)
    if m:
        return f'ok {m.group(1)}#{"usize" if m.group(2) == "USIZE" else "u8"}'

    # Ranges and slices
    if name == 'core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next':
        return 'core.iter.range.IteratorRange.next core.iter.range.StepUsize'
    if name == 'core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter':
        return 'fun r => ok r'
    if re.fullmatch(r'core\.slice\.Slice\w+\.len\w+', name):
        return 'fun s => ok (Slice.len s)'
    if name == 'core.slice.SliceU8.copy_from_sliceU8':
        return 'fun dst src => if src.length = dst.length then ok src else fail .panic'

    # ctutils
    if name.startswith('ctutils.traits.ct_eq.Sliceu8_CtEq_Sliceu8.ct_eq'):
        return 'fun a b => ok (decide (a.val = b.val))'

    # `NttPolynomial::from(Array)` (through core's blanket `Into`) wraps the array, and Aeneas erases
    # single-field wrappers.
    if name == 'hybrid_array.Array_Elem_BaseField_U256.Insts.CoreConvertIntoNttPolynomial_BaseField.into':
        return 'fun a => ok a'

    # hybrid-array: `Array<T, U>` is a wrapper around `[T; N]`, so these are the `[T; N]` operations.
    if name.startswith('hybrid_array.'):
        if re.search(r'\.deref_mut_', name):
            return 'fun a => ok (Array.to_slice_mut a)'
        if re.search(r'\.(as_slice|as_ref|deref)_', name):
            return 'fun a => ok (Array.to_slice a)'
        if re.search(r'_IndexMut_usize\.index_mut_', name):
            return 'fun a i => Array.index_mut_usize a i'
        if re.search(r'_Index_usize\.index_', name):
            return 'fun a i => Array.index_usize a i'
        if re.search(r'_Index_RangeTo_usize\.index_', name):
            return 'fun a r => Slice.subslice (Array.to_slice a) { start := 0#usize, «end» := r.«end» }'
        if re.search(r'_Index_RangeFrom_usize\.index_', name):
            return f'fun a r => Slice.subslice (Array.to_slice a) {{ start := r.start, «end» := {array_size(ty)}#usize }}'
        if re.search(r'_Index_Range_usize\.index_', name):
            return 'fun a r => Slice.subslice (Array.to_slice a) r'
        if re.search(r'_Index_RangeFull\.index_', name):
            return 'fun a _ => ok (Array.to_slice a)'
        if re.search(r'_Clone\.clone_', name):
            return 'fun a => ok a'
        if re.search(r'_Default\.default_', name):
            return f'ok {default_value(res.removeprefix("Result "))}'
        if re.search(r'_PartialEq_\w+\.eq_', name):
            return 'fun a b => ok (decide (a = b))'
        if name.startswith('hybrid_array.flatten.'):
            return 'fun a => ok (Model.flatten a)'
        if re.search(r'\.concat_', name):
            return 'fun a b => ok (Model.concat a b)'
        if re.search(r'\.(split|split_ref)_', name):
            return 'fun a => ok (Model.split a)'
        if re.search(r'\.from_slice_', name):
            return f'fun s => if h : s.val.length = {array_size(res)} then ok (Array.from s.val (by simp [h])) else fail .panic'
        if re.search(r'_CtSelect\.ct_select_', name):
            return 'fun a b c => ok (if c then b else a)'

    # sha3: hashers hold the absorbed message, and hash it when finalized.
    if re.fullmatch(r'digest\.digest\.Sha3_(256|512)_Digest\.new_\w+', name):
        return 'ok []'
    if re.fullmatch(r'digest\.digest\.Sha3_(256|512)_Digest\.update_\w+', name):
        return 'fun h x => ok (h ++ x.val)'
    if re.fullmatch(r'digest\.digest\.Sha3_512_Digest\.finalize_\w+', name):
        return 'fun h => ok (Model.ofByteVec (SHA3.sha3_512 (Model.toByteVec h)))'
    if re.fullmatch(r'digest\.digest\.Sha3_256_Digest\.finalize_into_\w+', name):
        return 'fun h _ => ok (Model.ofByteVec (SHA3.sha3_256 (Model.toByteVec h)))'

    # shake: SHAKE256 (rate 136) hashers hold the absorbed message, and readers additionally the
    # number of bytes read; SHAKE128 (rate 168) ones are the spec's incremental sponge.
    if re.search(r'_Destruct\.drop_glue', name):
        return 'fun x => ok x'
    if name.startswith('shake.Shake_136_Default.'):
        return 'ok []'
    if name.startswith('shake.Shake_168_Default.'):
        return 'ok SHA3.SHAKE128.init'
    if name.startswith('shake.Shake_136_Update.'):
        return 'fun h x => ok (h ++ x.val)'
    if name.startswith('shake.Shake_168_Update.'):
        return 'fun h x => ok (SHA3.SHAKE128.absorb h (Model.toByteVec x.val))'
    if name.startswith('shake.Shake_136_ExtendableOutput.'):
        return 'fun h => ok (h, 0)'
    if name.startswith('shake.Shake_168_ExtendableOutput.'):
        return 'fun h => ok (SHA3.SHAKE128.finalize h)'
    if name.startswith('shake.ShakeReader_136_XofReader.'):
        return 'fun r out => ok (Model.shake256Read r out)'
    if name.startswith('shake.ShakeReader_168_XofReader.'):
        return 'fun r out => ok (Model.shake128Read r out)'

    raise SystemExit(f'gen_funs_external.py: no model for external function `{name} : {ty}`')


PRELUDE = '''\
-- AUTOGENERATED from FunsExternal_Template.lean by `scripts/gen_funs_external.py`. Do not edit.
--
-- Models of the external (non-extracted) functions used by `ExtractedRust.Funs`. These are part of
-- our trusted base; see `TrustBase.lean`.
import Aeneas
import ExtractedRust.Types
import Wychelean.Hashes.SHA3.XOF.Basic
open Aeneas Aeneas.Std Result ControlFlow Error
open Wychelean.Hashes
open RustMlKem

namespace RustMlKem.Model

/-- The number of ones in the binary representation of `n`. -/
def popcount (n : Nat) : Nat := (Nat.bits n).count true

/-- A list of bytes as a byte vector of the spec. -/
def toByteVec (l : List Std.U8) : Wychelean.ByteVec l.length :=
  Vector.ofFn fun i => UInt8.ofBitVec l[i].bv

/-- A byte vector of the spec as an array of bytes. -/
def ofByteVec {n : Usize} (v : Wychelean.ByteVec n.val) : Std.Array Std.U8 n :=
  Array.from (v.toList.map fun x => ⟨x.toBitVec⟩) (by simp)

/-- `[a, b].concat()`, as `hybrid_array::Array::concat`. -/
def concat {α : Type} {n m k : Usize} (a : Std.Array α n) (b : Std.Array α m)
    (h : n.val + m.val = k.val := by decide) : Std.Array α k :=
  Array.from (a.val ++ b.val) (by simp [h])

/-- Concatenate an array of arrays, as `hybrid_array::Array::flatten`. -/
def flatten {α : Type} {n k m : Usize} (a : Std.Array (Std.Array α n) k)
    (h : k.val * n.val = m.val := by decide) : Std.Array α m :=
  Array.from (a.val.map (·.val)).flatten (by
    rw [List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => n.val) (fun x _ => x.property)]
    simp [h])

/-- Split an array into two, as `hybrid_array::Array::split`. -/
def split {α : Type} {n m k : Usize} (a : Std.Array α k) (h : n.val + m.val = k.val := by decide) :
    Std.Array α n × Std.Array α m :=
  (Array.from (a.val.take n.val) (by simp; omega), Array.from (a.val.drop n.val) (by simp; omega))

/-- Read `out.length` more bytes of SHAKE256 output, given the message and the number of bytes read so
far. -/
def shake256Read (r : shake.ShakeReader_136) (out : Slice Std.U8) : shake.ShakeReader_136 × Slice Std.U8 :=
  let (msg, pos) := r
  ((msg, pos + out.length),
    Slice.from (((SHA3.shake256 (toByteVec msg) (pos + out.length)).toList.drop pos).map fun x => ⟨x.toBitVec⟩)
      (by simpa using out.property))

/-- Squeeze `out.length` more bytes of SHAKE128 output. -/
def shake128Read (r : shake.ShakeReader_168) (out : Slice Std.U8) : shake.ShakeReader_168 × Slice Std.U8 :=
  let (r, bytes) := SHA3.SHAKE128.squeeze r out.length
  (r, Slice.from (bytes.toList.map fun x => ⟨x.toBitVec⟩) (by simpa using out.property))

end RustMlKem.Model

open RustMlKem.Model
'''

out = [PRELUDE]
for name, ty, doc, attr in decls:
    out.append(f'{doc}\n{attr}\ndef {name} : {ty} :=\n  {model(name, ty)}\n')
open(out_path, 'w').write('\n'.join(out))
print(f'gen_funs_external.py: modelled {len(decls)} external functions', file=sys.stderr)
