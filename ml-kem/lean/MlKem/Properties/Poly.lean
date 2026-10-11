import MlKem.Properties.Arith
import Wychelean.KEM.MLKEM.Properties.Loops

/-! # Polynomial, vector and matrix arithmetic

Specs of the ring operations of `module_lattice::algebra` (at `BaseField`), and of
`MultiplyNtt for BaseField` (`ml_kem::algebra`): `MultiplyNTTs` of the spec.

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

/-- Unfolds the models of the external functions (hybrid-array indexing, `Default`, slices, ranges). -/
macro "unfold_ext" : tactic => `(tactic| simp only [hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.algebra.Polynomial_BaseField_Default.default_BaseFieldBaseField,
    module_lattice.algebra.NttPolynomial_BaseField_Default.default_BaseFieldBaseField,
    module_lattice.algebra.NttPolynomial_BaseField.new_BaseFieldBaseField,
    module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField,
    aeneas_mono.array_index_mut_Elem_BaseField_128, aeneas_mono.array_index_Elem_BaseField_128,
    hybrid_array.Array_Polynomial_BaseField_U2_Index_usize.index_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2,
    hybrid_array.Array_Polynomial_BaseField_U2_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Default.default_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Index_usize.index_NttPolynomial_BaseField_usize_U2NttPolynomial_BaseFieldUsizeU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U2NttPolynomial_BaseFieldUsizeU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Default.default_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Deref.deref_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    hybrid_array.Array_NttVector_BaseField_U2_U2_Index_usize.index_NttVector_BaseField_U2_usize_U2NttVector_BaseField_U2UsizeU2,
    module_lattice.algebra.Vector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    module_lattice.algebra.NttVector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U3_Index_usize.index_Polynomial_BaseField_usize_U3Polynomial_BaseFieldUsizeU3,
    hybrid_array.Array_Polynomial_BaseField_U3_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U3Polynomial_BaseFieldUsizeU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Default.default_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Index_usize.index_NttPolynomial_BaseField_usize_U3NttPolynomial_BaseFieldUsizeU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U3NttPolynomial_BaseFieldUsizeU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Default.default_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Deref.deref_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    hybrid_array.Array_NttVector_BaseField_U3_U3_Index_usize.index_NttVector_BaseField_U3_usize_U3NttVector_BaseField_U3UsizeU3,
    module_lattice.algebra.Vector_BaseField_U3_Default.default_BaseField_U3BaseFieldU3,
    module_lattice.algebra.NttVector_BaseField_U3_Default.default_BaseField_U3BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U4_Index_usize.index_Polynomial_BaseField_usize_U4Polynomial_BaseFieldUsizeU4,
    hybrid_array.Array_Polynomial_BaseField_U4_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U4Polynomial_BaseFieldUsizeU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Default.default_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Index_usize.index_NttPolynomial_BaseField_usize_U4NttPolynomial_BaseFieldUsizeU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U4NttPolynomial_BaseFieldUsizeU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Default.default_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Deref.deref_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    hybrid_array.Array_NttVector_BaseField_U4_U4_Index_usize.index_NttVector_BaseField_U4_usize_U4NttVector_BaseField_U4UsizeU4,
    module_lattice.algebra.Vector_BaseField_U4_Default.default_BaseField_U4BaseFieldU4,
    module_lattice.algebra.NttVector_BaseField_U4_Default.default_BaseField_U4BaseFieldU4,
    bind_tc_ok])


/-! ## Generic loop specs -/

/-- Spec of a Rust loop `for i in start..n { out[i] = f(i) }`, given by its unfolding equation. -/
theorem map_loop_spec {α : Type} {n : Usize} [Inhabited α]
    (loop : core.ops.range.Range Usize → Std.Array α n → Result (Std.Array α n))
    (f : Usize → Result α) (P : ℕ → α → Prop)
    (hloop : ∀ iter out, loop iter out = (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok out
      | some i => do
        let x ← f i
        let (_, back) ← Array.index_mut_usize out i
        loop iter1 (back x)))
    (hf : ∀ i : Usize, i.val < n.val → f i ⦃ x => P i.val x ⦄)
    (iter : core.ops.range.Range Usize) (out : Std.Array α n)
    (hend : iter.end.val = n.val) (hs : iter.start.val ≤ n.val)
    (hout : ∀ j < iter.start.val, P j out.val[j]!) :
    loop iter out ⦃ r => ∀ j < n.val, P j r.val[j]! ⦄ := by
  rw [hloop]
  by_cases hlt : iter.start.val < n.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    let* ⟨ x, hx ⟩ ← hf
    let* ⟨ _, back, _, hback ⟩ ← Array.index_mut_usize_spec
    subst hback
    apply map_loop_spec loop f P hloop hf iter1 _ (by rw [h2, hend]) (by scalar_tac)
    intro j hj
    by_cases hj' : j = iter.start.val
    · subst hj'; simp_lists [*]
    · have := hout j (by omega); simp_lists [*] at this ⊢; exact this
  · let* ⟨ o, iter1, ho, h1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst ho
    simp only [WP.spec_ok]
    intro j hj; exact hout j (by omega)
termination_by n.val - iter.start.val
decreasing_by scalar_decr_tac

/-- Spec of a Rust loop `for i in start..n { acc = f(i, acc) }`, given by its unfolding equation. -/
theorem fold_loop_spec {β : Type} (n : ℕ)
    (loop : core.ops.range.Range Usize → β → Result β)
    (f : Usize → β → Result β) (P : ℕ → β → Prop)
    (hloop : ∀ iter acc, loop iter acc = (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok acc
      | some i => do
        let acc1 ← f i acc
        loop iter1 acc1))
    (hf : ∀ (i : Usize) acc, i.val < n → P i.val acc → f i acc ⦃ acc' => P (i.val + 1) acc' ⦄)
    (iter : core.ops.range.Range Usize) (acc : β)
    (hend : iter.end.val = n) (hs : iter.start.val ≤ n) (hacc : P iter.start.val acc) :
    loop iter acc ⦃ r => P n r ⦄ := by
  rw [hloop]
  by_cases hlt : iter.start.val < n
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    let* ⟨ acc1, hacc1 ⟩ ← hf
    rw [← h1] at hacc1
    exact fold_loop_spec n loop f P hloop hf iter1 _ (by rw [h2, hend]) (by scalar_tac) hacc1
  · let* ⟨ o, iter1, ho, h1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst ho
    simp only [WP.spec_ok]
    have : iter.start.val = n := by omega
    rw [this] at hacc; exact hacc
termination_by n - iter.start.val
decreasing_by scalar_decr_tac

/-! ## Abstraction helpers -/

theorem Arr.getElem!_eq {α : Type} [Inhabited α] {n : Usize} (a : Std.Array α n) (j : ℕ) (hj : j < n.val) :
    a.val[j]! = a.val[j]'(by scalar_tac) := getElem!_pos a.val j (by scalar_tac)

theorem Coeffs.getElem!_eq (a : Coeffs) (j : ℕ) (hj : j < 256) :
    a.val[j]! = a.val[j]'(by scalar_tac) := getElem!_pos a.val j (by scalar_tac)

theorem Coeffs.Bounded.get! {m : ℕ} {a : Coeffs} (h : a.Bounded m) (j : ℕ) (hj : j < 256) :
    a.val[j]!.val < m := by
  rw [Coeffs.getElem!_eq a j hj]; exact h _ (List.getElem_mem _)

theorem Coeffs.Bounded.get {m : ℕ} {a : Coeffs} (h : a.Bounded m) (j : ℕ) (hj : j < a.val.length) :
    (a.val[j]'hj).val < m := h _ (List.getElem_mem hj)

theorem Coeffs.bounded_of {m : ℕ} {a : Coeffs} (h : ∀ j < 256, a.val[j]!.val < m) : a.Bounded m := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < 256 := by scalar_tac
  have := h j hj'
  rwa [Coeffs.getElem!_eq a j hj'] at this

theorem Coeffs.getElem_toVector (m : ℕ) (a : Coeffs) (j : ℕ) (hj : j < 256) :
    (a.toVector m)[j] = ((a.val[j]!.val : ℕ) : ZMod m) := by
  simp [Coeffs.toVector, toZMod, Coeffs.getElem!_eq a j hj]

theorem Coeffs.getElem_toTq (a : Coeffs) (j : ℕ) (hj : j < 256) :
    a.toTq[j] = ((a.val[j]!.val : ℕ) : Zq) := Coeffs.getElem_toVector q a j hj

theorem Coeffs.getElem_toPoly (m : ℕ) (a : Coeffs) (j : ℕ) (hj : j < 256) :
    (a.toPoly m)[j] = ((a.val[j]!.val : ℕ) : ZMod m) := Coeffs.getElem_toVector m a j hj

theorem poly_getElem_add {m : ℕ} (f g : Wychelean.KEM.MLKEM.Polynomial m) (i : ℕ) (hi : i < 256) :
    (f + g)[i] = f[i] + g[i] := Vector.getElem_zipWith ..

theorem poly_getElem_sub {m : ℕ} (f g : Wychelean.KEM.MLKEM.Polynomial m) (i : ℕ) (hi : i < 256) :
    (f - g)[i] = f[i] - g[i] := Vector.getElem_zipWith ..

theorem tq_getElem_add (f g : Tq) (i : ℕ) (hi : i < 256) :
    (f + g)[i] = f[i] + g[i] := Vector.getElem_zipWith ..

theorem cast_mod_q (a : ℕ) : ((a % 3329 : ℕ) : Zq) = a := ZMod.natCast_mod a q

/-! ## Polynomial operations -/

theorem poly_add_loop_spec (a b : Coeffs) (ha : a.Bounded q) (hb : b.Bounded q)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 256) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField_loop iter a b out
      ⦃ r => ∀ j < 256, r.val[j]!.val = (a.val[j]!.val + b.val[j]!.val) % 3329 ⦄ := by
  apply map_loop_spec (α := U16) (n := 256#usize)
    (module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField_loop · a b)
    (fun i => do
      let x ← Array.index_usize a i
      let y ← Array.index_usize b i
      module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : U16) => x.val = (a.val[j]!.val + b.val[j]!.val) % 3329)
  · intro iter out
    rw [module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := ha.get i.val (by scalar_tac)
    have := hb.get i.val (by scalar_tac)
    rw [Coeffs.getElem!_eq a _ (by scalar_tac), Coeffs.getElem!_eq b _ (by scalar_tac)]
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem poly_add_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = a.toPoly + b.toPoly ⦄ := by
  unfold module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField
  unfold_ext
  step with poly_add_loop_spec as ⟨ r, hr ⟩
  refine ⟨Coeffs.bounded_of fun j hj => by rw [hr j hj]; show _ < 3329; omega, ?_⟩
  refine Polynomial.ext fun j hj => ?_
  rw [poly_getElem_add, Coeffs.getElem_toPoly q r j hj, Coeffs.getElem_toPoly q a j hj,
    Coeffs.getElem_toPoly q b j hj, hr j hj, cast_mod_q, Nat.cast_add]

theorem cast_sub_q (a b : ℕ) (hb : b < 3329) : (((a + 3329 - b) % 3329 : ℕ) : Zq) = a - b := by
  rw [cast_mod_q, Nat.cast_sub (by omega), Nat.cast_add]
  have : ((3329 : ℕ) : Zq) = 0 := ZMod.natCast_self q
  rw [this, add_zero]

theorem poly_sub_loop_spec (a b : Coeffs) (ha : a.Bounded q) (hb : b.Bounded q)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 256) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField_loop iter a b out
      ⦃ r => ∀ j < 256, r.val[j]!.val = (a.val[j]!.val + 3329 - b.val[j]!.val) % 3329 ⦄ := by
  apply map_loop_spec (α := U16) (n := 256#usize)
    (module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField_loop · a b)
    (fun i => do
      let x ← Array.index_usize a i
      let y ← Array.index_usize b i
      module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField x y)
    (fun j (x : U16) => x.val = (a.val[j]!.val + 3329 - b.val[j]!.val) % 3329)
  · intro iter out
    rw [module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := ha.get i.val (by scalar_tac)
    have := hb.get i.val (by scalar_tac)
    rw [Coeffs.getElem!_eq a _ (by scalar_tac), Coeffs.getElem!_eq b _ (by scalar_tac)]
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem poly_sub_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = a.toPoly - b.toPoly ⦄ := by
  unfold module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField
  unfold_ext
  step with poly_sub_loop_spec as ⟨ r, hr ⟩
  refine ⟨Coeffs.bounded_of fun j hj => by rw [hr j hj]; show _ < 3329; omega, ?_⟩
  refine Polynomial.ext fun j hj => ?_
  rw [poly_getElem_sub, Coeffs.getElem_toPoly q r j hj, Coeffs.getElem_toPoly q a j hj,
    Coeffs.getElem_toPoly q b j hj, hr j hj, cast_sub_q _ _ (hb.get! j hj)]

theorem elem_mul_poly_loop_spec (c : U16) (a : Coeffs) (hc : c.val < q) (ha : a.Bounded q)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 256) (hs : iter.start.val = 0) :
    module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField_loop iter c a out
      ⦃ r => ∀ j < 256, r.val[j]!.val = (c.val * a.val[j]!.val) % 3329 ⦄ := by
  apply map_loop_spec (α := U16) (n := 256#usize)
    (module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField_loop · c a)
    (fun i => do
      let x ← Array.index_usize a i
      module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField c x)
    (fun j (x : U16) => x.val = (c.val * a.val[j]!.val) % 3329)
  · intro iter out
    rw [module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := ha.get i.val (by scalar_tac)
    rw [Coeffs.getElem!_eq a _ (by scalar_tac)]
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem elem_mul_poly_spec (c : U16) (a : Coeffs)
    (hc : c.val < q) (ha : a.Bounded q) :
    module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField c a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q = toZq c • a.toVector q ⦄ := by
  unfold module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField
  unfold_ext
  step with elem_mul_poly_loop_spec as ⟨ r, hr ⟩
  refine ⟨Coeffs.bounded_of fun j hj => by rw [hr j hj]; show _ < 3329; omega, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_smul, Coeffs.getElem_toVector q r j hj, Coeffs.getElem_toVector q a j hj,
    hr j hj, cast_mod_q, Nat.cast_mul]
  rfl

theorem ntt_poly_add_loop_spec (a b : Coeffs) (ha : a.Bounded q) (hb : b.Bounded q)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 256) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField_loop iter a b out
      ⦃ r => ∀ j < 256, r.val[j]!.val = (a.val[j]!.val + b.val[j]!.val) % 3329 ⦄ := by
  apply map_loop_spec (α := U16) (n := 256#usize)
    (module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField_loop · a b)
    (fun i => do
      let x ← Array.index_usize a i
      let y ← Array.index_usize b i
      module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : U16) => x.val = (a.val[j]!.val + b.val[j]!.val) % 3329)
  · intro iter out
    rw [module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := ha.get i.val (by scalar_tac)
    have := hb.get i.val (by scalar_tac)
    rw [Coeffs.getElem!_eq a _ (by scalar_tac), Coeffs.getElem!_eq b _ (by scalar_tac)]
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_poly_add_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq + b.toTq ⦄ := by
  unfold module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField
  unfold_ext
  step with ntt_poly_add_loop_spec as ⟨ r, hr ⟩
  refine ⟨Coeffs.bounded_of fun j hj => by rw [hr j hj]; show _ < 3329; omega, ?_⟩
  refine Tq.ext fun j hj => ?_
  rw [tq_getElem_add, Coeffs.getElem_toTq r j hj, Coeffs.getElem_toTq a j hj,
    Coeffs.getElem_toTq b j hj, hr j hj, cast_mod_q, Nat.cast_add]

/-! ## The tables `ZETA_POW_BITREV` and `GAMMA`, and `MultiplyNTTs` -/

theorem barrett_reduce_wide_spec (x : U32) (h : x.val ≤ 2 * 3328 * 3328) :
    algebra.BaseField_Field.barrett_reduce x ⦃ r => r.val = x.val % 3329 ⦄ := by
  unfold algebra.BaseField_Field.barrett_reduce
  step*
  all_goals
    have hq : quotient.val = x.val * 5039 / 2 ^ 24 := by
      rw [quotient_post, product_post, x1_post, i_post, i1_post, Nat.shiftRight_eq_div_pow]
    simp only [QLL_val] at *
    scalar_tac

theorem bitRev7_formula : ∀ n < 128, Wychelean.bitRev 7 n =
    ((((((n >>> 6) % 2 ||| ((n >>> 5) % 2) <<< 1) ||| ((n >>> 4) % 2) <<< 2) |||
      ((n >>> 3) % 2) <<< 3) ||| ((n >>> 2) % 2) <<< 4) ||| ((n >>> 1) % 2) <<< 5) |||
      (n % 2) <<< 6 := by
  decide

theorem shl_small (a s : ℕ) (ha : a < 2) (hs : s < 7) : a <<< s % Usize.size = a <<< s := by
  apply Nat.mod_eq_of_lt
  have : a <<< s < 2 ^ 7 := by interval_cases s <;> interval_cases a <;> decide
  have : 2 ^ 7 ≤ Usize.size := by scalar_tac
  omega

theorem bitrev7_spec (x : Usize) (hx : x.val < 128) :
    algebra.ZETA_POW_BITREV.bitrev7 x ⦃ r => r.val = Wychelean.bitRev 7 x.val ⦄ := by
  unfold algebra.ZETA_POW_BITREV.bitrev7
  step*
  all_goals try (rcases System.Platform.numBits_eq with h | h <;> simp [h] <;> done)
  have h4 : i4.val = i3.val <<< 1 := by rw [i4_post]; exact shl_small _ _ (by omega) (by omega)
  have h8 : i8.val = i7.val <<< 2 := by rw [i8_post]; exact shl_small _ _ (by omega) (by omega)
  have h12 : i12.val = i11.val <<< 3 := by rw [i12_post]; exact shl_small _ _ (by omega) (by omega)
  have h16 : i16.val = i15.val <<< 4 := by rw [i16_post]; exact shl_small _ _ (by omega) (by omega)
  have h20 : i20.val = i19.val <<< 5 := by rw [i20_post]; exact shl_small _ _ (by omega) (by omega)
  have h23 : i23.val = i22.val <<< 6 := by rw [i23_post]; exact shl_small _ _ (by omega) (by omega)
  rw [bitRev7_formula _ hx]
  simp only [UScalar.val_or, h4, h8, h12, h16, h20, h23, i_post, i1_post, i2_post, i3_post, i5_post,
    i6_post, i7_post, i9_post, i10_post, i11_post, i13_post, i14_post, i15_post, i17_post,
    i18_post, i19_post, i21_post, i22_post]

theorem ZETA_POW_BITREV_ZETA_eq : algebra.ZETA_POW_BITREV.ZETA = 17#u64 := by
  unfold algebra.ZETA_POW_BITREV.ZETA; rfl

theorem GAMMA_ZETA_eq : algebra.GAMMA.ZETA = 17#u64 := by
  unfold algebra.GAMMA.ZETA; rfl

theorem QLL_eq : algebra.BaseField_Field.QLL = 3329#u64 := by
  unfold algebra.BaseField_Field.QLL; rfl

theorem and_65535 (x : ℕ) (hx : x < 2 ^ 16) : x &&& 65535 = x := by
  have := Nat.and_two_pow_sub_one_eq_mod x 16
  rw [show (2 : ℕ) ^ 16 - 1 = 65535 by rfl] at this
  rw [this, Nat.mod_eq_of_lt hx]

theorem zeta_pow_loop0_spec (pow : Std.Array U16 128#usize) (i : Usize) (curr : U64)
    (hi : i.val ≤ 128) (hcurr : curr.val = 17 ^ i.val % 3329)
    (hpow : ∀ j < i.val, pow.val[j]!.val = 17 ^ j % 3329) :
    algebra.ZETA_POW_BITREV_loop0 pow i curr ⦃ r => ∀ j < 128, r.val[j]!.val = 17 ^ j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV_loop0
  unfold_ext
  split
  · have hc : curr.val < 3329 := by rw [hcurr]; exact Nat.mod_lt _ (by omega)
    simp only [ZETA_POW_BITREV_ZETA_eq, QLL_eq]
    step*
    have hi2 : i2.val = 17 ^ i.val % 3329 := by
      rw [i2_post, UScalar.cast_val_eq, i1_post, UScalar.val_and, show (65535#u64).val = 65535 by rfl,
        and_65535 _ (by omega)]
      simp only [UScalarTy.U16_numBits_eq]
      rw [Nat.mod_eq_of_lt (by omega), hcurr]
    intro j hj
    rw [array_index_mut_Elem_BaseField_128_back_post]
    by_cases hj' : j = i.val
    · subst hj'; simp_lists [hi2]
    · have := hpow j (by omega); simp_lists [*] at this ⊢; exact this
  · simp only [WP.spec_ok]
    intro j hj; exact hpow j (by scalar_tac)
termination_by 128 - i.val
decreasing_by scalar_decr_tac

theorem zeta_pow_loop1_spec (pow pow_bitrev : Std.Array U16 128#usize) (i : Usize)
    (hi : i.val ≤ 128) (hpow : ∀ j < 128, pow.val[j]!.val = 17 ^ j % 3329)
    (hpb : ∀ j < i.val, pow_bitrev.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329) :
    algebra.ZETA_POW_BITREV_loop1 pow pow_bitrev i
      ⦃ r => ∀ j < 128, r.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV_loop1
  unfold_ext
  split
  · let* ⟨ i1, hi1 ⟩ ← bitrev7_spec
    have hb : i1.val < 128 := by rw [hi1]; exact Wychelean.bitRev_lt 7 i.val
    step*
    intro j hj
    rw [array_index_mut_Elem_BaseField_128_back_post]
    by_cases hj' : j = i.val
    · subst hj'
      have := hpow i1.val hb
      rw [Arr.getElem!_eq pow _ hb] at this
      simp_lists [*]
    · have := hpb j (by omega); simp_lists [*] at this ⊢; exact this
  · simp only [WP.spec_ok]
    intro j hj; exact hpb j (by scalar_tac)
termination_by 128 - i.val
decreasing_by scalar_decr_tac

/-- The table `ZETA_POW_BITREV`: `ZETA_POW_BITREV[i] = ζ^BitRev₇(i)`. -/
@[step] theorem zeta_pow_bitrev_val :
    algebra.ZETA_POW_BITREV ⦃ z => ∀ j < 128, z.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV
  unfold_ext
  step with zeta_pow_loop0_spec as ⟨ pow1, hpow1 ⟩
  step with zeta_pow_loop1_spec as ⟨ z, hz ⟩
  simp_all

theorem gamma_loop_spec (gamma : Std.Array U16 128#usize) (i : Usize) (hi : i.val ≤ 128)
    (hg : ∀ j < i.val, gamma.val[j]!.val =
      (17 ^ Wychelean.bitRev 7 j % 3329) * (17 ^ Wychelean.bitRev 7 j % 3329) * 17 % 3329) :
    algebra.GAMMA_loop gamma i
      ⦃ r => ∀ j < 128, r.val[j]!.val =
        (17 ^ Wychelean.bitRev 7 j % 3329) * (17 ^ Wychelean.bitRev 7 j % 3329) * 17 % 3329 ⦄ := by
  unfold algebra.GAMMA_loop
  unfold_ext
  split
  · simp only [GAMMA_ZETA_eq, QLL_eq]
    let* ⟨ a, ha ⟩ ← zeta_pow_bitrev_val
    have hai := ha i.val (by scalar_tac)
    rw [Arr.getElem!_eq a _ (by scalar_tac)] at hai
    have hlt : (17 ^ Wychelean.bitRev 7 i.val % 3329) < 3329 := Nat.mod_lt _ (by omega)
    step*
    have hz : zpr.val = 17 ^ Wychelean.bitRev 7 i.val % 3329 := by
      rw [zpr_post, UScalar.cast_val_eq, ebf_post, hai]
      simp only [UScalarTy.U64_numBits_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hg' : g.val < 3329 := by rw [g_post]; exact Nat.mod_lt _ (by omega)
    have hi4 : i4.val = (17 ^ Wychelean.bitRev 7 i.val % 3329) * (17 ^ Wychelean.bitRev 7 i.val % 3329)
        * 17 % 3329 := by
      rw [i4_post, UScalar.cast_val_eq, i3_post, UScalar.val_and, show (65535#u64).val = 65535 by rfl,
        and_65535 _ (by omega)]
      simp only [UScalarTy.U16_numBits_eq]
      rw [Nat.mod_eq_of_lt (by omega), g_post, i2_post, i1_post, hz]
    intro j hj
    rw [array_index_mut_Elem_BaseField_128_back_post]
    by_cases hj' : j = i.val
    · subst hj'; simp_lists [hi4]
    · have := hg j (by omega); simp_lists [*] at this ⊢; exact this
  · simp only [WP.spec_ok]
    intro j hj; exact hg j (by scalar_tac)
termination_by 128 - i.val
decreasing_by scalar_decr_tac

/-- The table `GAMMA`: `GAMMA[i] = ζ^(2·BitRev₇(i)+1)`. -/
@[step] theorem gamma_val :
    algebra.GAMMA ⦃ g => ∀ j < 128, g.val[j]!.val =
      (17 ^ Wychelean.bitRev 7 j % 3329) * (17 ^ Wychelean.bitRev 7 j % 3329) * 17 % 3329 ⦄ := by
  unfold algebra.GAMMA
  unfold_ext
  step with gamma_loop_spec as ⟨ g, hg ⟩
  simp_all

theorem cast_pow17 (k : ℕ) : ((17 ^ k % 3329 : ℕ) : Zq) = ζ ^ k := by
  rw [cast_mod_q]; push_cast; rfl

theorem cast_gamma (k : ℕ) :
    (((17 ^ k % 3329) * (17 ^ k % 3329) * 17 % 3329 : ℕ) : Zq) = ζ ^ (2 * k + 1) := by
  rw [cast_mod_q]; push_cast
  rw [cast_pow17]
  have : (17 : Zq) = ζ := rfl
  rw [this]; ring

@[step] theorem base_case_multiply_spec (a0 a1 b0 b1 : U16) (i : Usize)
    (ha0 : a0.val < 3329) (ha1 : a1.val < 3329) (hb0 : b0.val < 3329) (hb1 : b1.val < 3329)
    (hi : i.val < 128) :
    algebra.base_case_multiply a0 a1 b0 b1 i ⦃ c0 c1 =>
      c0.val < 3329 ∧ c1.val < 3329 ∧
      ((c0.val : ℕ) : Zq) = (a0.val : Zq) * b0.val + (a1.val : Zq) * b1.val * ζ ^ (2 * Wychelean.bitRev 7 i.val + 1) ∧
      ((c1.val : ℕ) : Zq) = (a0.val : Zq) * b1.val + (a1.val : Zq) * b0.val ⦄ := by
  unfold algebra.base_case_multiply
  unfold_ext
  simp only [lift]
  have hfa0 := core.convert.num.FromU32U16.from_val_eq a0
  have hfa1 := core.convert.num.FromU32U16.from_val_eq a1
  have hfb0 := core.convert.num.FromU32U16.from_val_eq b0
  have hfb1 := core.convert.num.FromU32U16.from_val_eq b1
  let* ⟨ a, ha ⟩ ← gamma_val
  have hga := ha i.val hi
  rw [Arr.getElem!_eq a _ (by scalar_tac)] at hga
  have hgl : (a.val[i.val]'(by scalar_tac)).val < 3329 := by rw [hga]; exact Nat.mod_lt _ (by omega)
  let* ⟨ ebf, hebf ⟩ ← Array.index_usize_spec
  have hfe := core.convert.num.FromU32U16.from_val_eq ebf
  let* ⟨ i1, hi1 ⟩ ← U32.mul_spec
  let* ⟨ i2, hi2 ⟩ ← barrett_reduce_spec
  have hfi2 := core.convert.num.FromU32U16.from_val_eq i2
  let* ⟨ i3, hi3 ⟩ ← U32.mul_spec
  let* ⟨ i4, hi4 ⟩ ← U32.mul_spec
  let* ⟨ i5, hi5 ⟩ ← U32.add_spec
  let* ⟨ c0, hc0 ⟩ ← barrett_reduce_wide_spec
  let* ⟨ i6, hi6 ⟩ ← U32.mul_spec
  let* ⟨ i7, hi7 ⟩ ← U32.mul_spec
  let* ⟨ i8, hi8 ⟩ ← U32.add_spec
  let* ⟨ c1, hc1 ⟩ ← barrett_reduce_wide_spec
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hc0, cast_mod_q, hi5, Nat.cast_add, hi3, hi4, hfa0, hfa1, hfb0, hfi2, hi2, Nat.cast_mul,
      Nat.cast_mul, cast_mod_q, hi1, hfb1, hfe, hebf, hga, Nat.cast_mul, cast_gamma]
    ring
  · rw [hc1, cast_mod_q, hi8, Nat.cast_add, hi6, hi7, hfa0, hfa1, hfb0, hfb1, Nat.cast_mul,
      Nat.cast_mul]

theorem tq_mul_even (a b : Tq) (i : ℕ) (hi : i < 128) :
    (a * b)[2 * i] = a[2 * i] * b[2 * i] + a[2 * i + 1] * b[2 * i + 1] * ζ ^ (2 * Wychelean.bitRev 7 i + 1) := by
  rw [mul_eq_multiply]
  show ((Vector.ofFn fun i : Fin 128 => NTT.baseCaseMultiply a[2 * i.val] a[2 * i.val + 1]
      b[2 * i.val] b[2 * i.val + 1] (ζ ^ (2 * Wychelean.bitRev 7 i.val + 1))).flatten)[2 * i] = _
  rw [Vector.getElem_flatten, Vector.getElem_ofFn]
  have e1 : (2 * i) / 2 = i := by omega
  have e2 : (2 * i) % 2 = 0 := by omega
  simp [e1, e2, NTT.baseCaseMultiply]

theorem tq_mul_odd (a b : Tq) (i : ℕ) (hi : i < 128) :
    (a * b)[2 * i + 1] = a[2 * i] * b[2 * i + 1] + a[2 * i + 1] * b[2 * i] := by
  rw [mul_eq_multiply]
  show ((Vector.ofFn fun i : Fin 128 => NTT.baseCaseMultiply a[2 * i.val] a[2 * i.val + 1]
      b[2 * i.val] b[2 * i.val + 1] (ζ ^ (2 * Wychelean.bitRev 7 i.val + 1))).flatten)[2 * i + 1] = _
  rw [Vector.getElem_flatten, Vector.getElem_ofFn]
  have e1 : (2 * i + 1) / 2 = i := by omega
  have e2 : (2 * i + 1) % 2 = 1 := by omega
  simp [e1, e2, NTT.baseCaseMultiply]

theorem multiply_ntt_loop_spec (a b : Coeffs) (ha : a.Bounded q) (hb : b.Bounded q)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 128) (hs : iter.start.val ≤ 128)
    (hout : ∀ j (hj : j < 256), j < 2 * iter.start.val →
      out.val[j]!.val < 3329 ∧ ((out.val[j]!.val : ℕ) : Zq) = (a.toTq * b.toTq)[j]) :
    algebra.BaseField_MultiplyNtt.multiply_ntt_loop iter a b out
      ⦃ r => ∀ j (hj : j < 256),
        r.val[j]!.val < 3329 ∧ ((r.val[j]!.val : ℕ) : Zq) = (a.toTq * b.toTq)[j] ⦄ := by
  rw [algebra.BaseField_MultiplyNtt.multiply_ntt_loop]
  unfold_ext
  by_cases hlt : iter.start.val < 128
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    step*
    case ha0 => rw [ebf_post]; exact ha.get _ _
    case ha1 => rw [ebf1_post]; exact ha.get _ _
    case hb0 => rw [ebf2_post]; exact hb.get _ _
    case hb1 => rw [ebf3_post]; exact hb.get _ _
    case hout =>
      intro j hj hj2
      rw [index_mut_Elem_BaseField_usize_U256_back1_post, index_mut_Elem_BaseField_usize_U256_back_post]
      simp only [i1_post, i2_post, i3_post] at ebf_post ebf1_post ebf2_post ebf3_post
      have e0 : (a.toTq * b.toTq)[2 * iter.start.val] = _ := tq_mul_even a.toTq b.toTq _ hlt
      have e1 : (a.toTq * b.toTq)[2 * iter.start.val + 1] = _ := tq_mul_odd a.toTq b.toTq _ hlt
      simp only [Coeffs.getElem_toTq _ _ (by omega : 2 * iter.start.val < 256),
        Coeffs.getElem_toTq _ _ (by omega : 2 * iter.start.val + 1 < 256),
        Coeffs.getElem!_eq _ _ (by omega : 2 * iter.start.val < 256),
        Coeffs.getElem!_eq _ _ (by omega : 2 * iter.start.val + 1 < 256)] at e0 e1
      by_cases hA : j = 2 * iter.start.val + 1
      · subst hA
        simp_lists
        refine ⟨c0_post1, ?_⟩
        rw [e1, c0_post3, ebf_post, ebf1_post, ebf2_post, ebf3_post]
      · by_cases hB : j = 2 * iter.start.val
        · subst hB
          simp_lists
          refine ⟨c0_post, ?_⟩
          rw [e0, c0_post2, ebf_post, ebf1_post, ebf2_post, ebf3_post]
        · have := hout j hj (by omega)
          simp_lists [*] at this ⊢
          exact this
  · let* ⟨ o, iter1, ho, h1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst ho
    simp only [WP.spec_ok]
    intro j hj; exact hout j hj (by omega)
termination_by 128 - iter.start.val
decreasing_by scalar_decr_tac

-- INTERFACE
@[step] theorem multiply_ntt_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    algebra.BaseField_MultiplyNtt.multiply_ntt a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq * b.toTq ⦄ := by
  unfold algebra.BaseField_MultiplyNtt.multiply_ntt
  unfold_ext
  step with multiply_ntt_loop_spec as ⟨ r, hr ⟩
  refine ⟨Coeffs.bounded_of fun j hj => (hr j hj).1, Tq.ext fun j hj => ?_⟩
  rw [Coeffs.getElem_toTq r j hj, (hr j hj).2]

-- INTERFACE
@[step] theorem ntt_poly_mul_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq * b.toTq ⦄ := by
  unfold module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField
  exact multiply_ntt_spec a b ha hb

/-! ## Vector helpers -/

theorem zero_coeffs_spec :
    Coeffs.Bounded q (Array.repeat 256#usize 0#u16) ∧ Coeffs.toTq (Array.repeat 256#usize 0#u16) = 0 := by
  refine ⟨fun x hx => ?_, Tq.ext fun j hj => ?_⟩
  · simp only [Array.repeat_val, List.mem_replicate] at hx
    rw [hx.2]; simp
  · rw [Coeffs.getElem_toTq _ j hj]
    have : (Array.repeat 256#usize 0#u16).val[j]! = 0#u16 := by
      rw [Coeffs.getElem!_eq _ j hj]; simp only [Array.repeat_val, List.getElem_replicate]
    rw [this]
    show _ = (Vector.replicate 256 0)[j]
    simp

theorem Vec.Bounded.get! {m : ℕ} {n : Usize} {v : Std.Array Coeffs n} (h : Vec.Bounded m v) (j : ℕ)
    (hj : j < n.val) : (v.val[j]!).Bounded m := by
  rw [Arr.getElem!_eq v j hj]; exact h _ (List.getElem_mem _)

theorem Vec.bounded_of {m : ℕ} {n : Usize} {v : Std.Array Coeffs n}
    (h : ∀ j < n.val, (v.val[j]!).Bounded m) : Vec.Bounded m v := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < n.val := by scalar_tac
  have := h j hj'
  rwa [Arr.getElem!_eq v j hj'] at this

theorem Mat.Bounded.get! {m : ℕ} {k l : Usize} {A : Std.Array (Std.Array Coeffs l) k} (h : Mat.Bounded m A)
    (j : ℕ) (hj : j < k.val) : Vec.Bounded m (A.val[j]!) := by
  rw [Arr.getElem!_eq A j hj]; exact h _ (List.getElem_mem _)

theorem getElem_toPolyVec (m : ℕ) {n : Usize} (v : Std.Array Coeffs n) (j : ℕ) (hj : j < n.val) :
    (toPolyVec m v)[j] = (v.val[j]!).toPoly m := by
  simp [toPolyVec, Arr.getElem!_eq v j hj]

theorem getElem_toNTTVec {n : Usize} (v : Std.Array Coeffs n) (j : ℕ) (hj : j < n.val) :
    (toNTTVec v)[j] = (v.val[j]!).toTq := by
  simp [toNTTVec, Arr.getElem!_eq v j hj]

theorem getElem_toNTTMat {k l : Usize} (A : Std.Array (Std.Array Coeffs l) k) (j : ℕ) (hj : j < k.val) :
    (toNTTMat A)[j] = toNTTVec (A.val[j]!) := by
  simp [toNTTMat, Arr.getElem!_eq A j hj]

/-- The partial sums of the inner product. -/
def partialIP {k : ℕ} (v w : Vector Tq k) (j : ℕ) : Tq :=
  ((Vector.zipWith (· * ·) v w).toList.take j).foldl (· + ·) 0

theorem partialIP_zero {k : ℕ} (v w : Vector Tq k) : partialIP v w 0 = 0 := by
  simp [partialIP]

theorem partialIP_succ {k : ℕ} (v w : Vector Tq k) (j : ℕ) (hj : j < k) :
    partialIP v w (j + 1) = partialIP v w j + v[j] * w[j] := by
  simp [partialIP, List.take_add_one, hj]

theorem partialIP_full {k : ℕ} (v w : Vector Tq k) :
    partialIP v w k = Wychelean.Utils.Linear.innerProduct v w := by
  rw [partialIP, List.take_of_length_le (by simp), Vector.foldl_toList]
  rfl

/-! ### Rank 2 -/

theorem vec_add_loop_spec_2 (v w : Vec2) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec2)
    (hend : iter.end.val = 2) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop iter v w out
      ⦃ r => ∀ j < 2, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toPoly q r.val[j]! = (v.val[j]!).toPoly + (w.val[j]!).toPoly ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 2#usize)
    (module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toPoly = (v.val[j]!).toPoly + (w.val[j]!).toPoly)
  · intro iter out
    rw [module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem vec_add_ref_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2
  unfold_ext
  step with vec_add_loop_spec_2 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toPolyVec q r j hj, getElem_toPolyVec q v j hj,
    getElem_toPolyVec q w j hj, (hr j hj).2]

-- INTERFACE
@[step] theorem vec_add_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U2_Add_Vector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.Vector_BaseField_U2_Add_Vector_BaseField_U2.add_BaseField_U2BaseFieldU2
  exact vec_add_ref_spec_2 v w hv hw

theorem ntt_vec_add_loop_spec_2 (v w : Vec2) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec2)
    (hend : iter.end.val = 2) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop iter v w out
      ⦃ r => ∀ j < 2, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = (v.val[j]!).toTq + (w.val[j]!).toTq ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 2#usize)
    (module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = (v.val[j]!).toTq + (w.val[j]!).toTq)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_vec_add_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2
  unfold_ext
  step with ntt_vec_add_loop_spec_2 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toNTTVec r j hj, getElem_toNTTVec v j hj,
    getElem_toNTTVec w j hj, (hr j hj).2]

theorem ntt_dot_loop_spec_2 (v w : Vec2) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 2) (hs : iter.start.val = 0) (hout : out.Bounded q ∧ out.toTq = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2_loop iter v w out
      ⦃ r => Coeffs.Bounded q r ∧ Coeffs.toTq r = partialIP (toNTTVec v) (toNTTVec w) 2 ⦄ := by
  apply fold_loop_spec (β := Coeffs) 2
    (module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2_loop · v w)
    (fun i acc => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      let z ← module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField x y
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField acc z)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = partialIP (toNTTVec v) (toNTTVec w) j)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2_loop]
    unfold_ext; simp; rfl
  · intro i acc hi hacc
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    have e := partialIP_succ (toNTTVec v) (toNTTVec w) i.val hi
    rw [getElem_toNTTVec v _ hi, getElem_toNTTVec w _ hi] at e
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · simpa [hs, partialIP_zero] using hout

-- INTERFACE
@[step] theorem ntt_dot_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2
  unfold_ext
  step with ntt_dot_loop_spec_2 as ⟨ r, hr1, hr2 ⟩
  · exact zero_coeffs_spec
  · exact ⟨hr1, by rw [← partialIP_full]; exact hr2⟩

theorem ntt_mat_mul_loop_spec_2 (A : Mat2) (v : Vec2) (hA : Mat.Bounded q A) (hv : Vec.Bounded q v)
    (iter : core.ops.range.Range Usize) (out : Vec2)
    (hend : iter.end.val = 2) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2_loop iter A v out
      ⦃ r => ∀ j < 2, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v) ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 2#usize)
    (module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2_loop · A v)
    (fun i => do
      let row ← Array.index_usize A i
      module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2 row v)
    (fun j (x : Coeffs) => x.Bounded q ∧
      x.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v))
  · intro iter out
    rw [module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hA.get! i.val hi
    rw [Arr.getElem!_eq A _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_2 (A : Mat2) (v : Vec2)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  unfold module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2
  unfold_ext
  step with ntt_mat_mul_loop_spec_2 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Wychelean.Utils.Linear.Mat.mulVec, Vector.getElem_map, getElem_toNTTVec r j hj,
    getElem_toNTTMat A j hj, (hr j hj).2]

/-! ### Rank 3 -/

theorem vec_add_loop_spec_3 (v w : Vec3) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec3)
    (hend : iter.end.val = 3) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop iter v w out
      ⦃ r => ∀ j < 3, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toPoly q r.val[j]! = (v.val[j]!).toPoly + (w.val[j]!).toPoly ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 3#usize)
    (module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toPoly = (v.val[j]!).toPoly + (w.val[j]!).toPoly)
  · intro iter out
    rw [module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem vec_add_ref_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3
  unfold_ext
  step with vec_add_loop_spec_3 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toPolyVec q r j hj, getElem_toPolyVec q v j hj,
    getElem_toPolyVec q w j hj, (hr j hj).2]

-- INTERFACE
@[step] theorem vec_add_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U3_Add_Vector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.Vector_BaseField_U3_Add_Vector_BaseField_U3.add_BaseField_U3BaseFieldU3
  exact vec_add_ref_spec_3 v w hv hw

theorem ntt_vec_add_loop_spec_3 (v w : Vec3) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec3)
    (hend : iter.end.val = 3) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop iter v w out
      ⦃ r => ∀ j < 3, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = (v.val[j]!).toTq + (w.val[j]!).toTq ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 3#usize)
    (module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = (v.val[j]!).toTq + (w.val[j]!).toTq)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_vec_add_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3
  unfold_ext
  step with ntt_vec_add_loop_spec_3 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toNTTVec r j hj, getElem_toNTTVec v j hj,
    getElem_toNTTVec w j hj, (hr j hj).2]

theorem ntt_dot_loop_spec_3 (v w : Vec3) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 3) (hs : iter.start.val = 0) (hout : out.Bounded q ∧ out.toTq = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3_loop iter v w out
      ⦃ r => Coeffs.Bounded q r ∧ Coeffs.toTq r = partialIP (toNTTVec v) (toNTTVec w) 3 ⦄ := by
  apply fold_loop_spec (β := Coeffs) 3
    (module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3_loop · v w)
    (fun i acc => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      let z ← module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField x y
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField acc z)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = partialIP (toNTTVec v) (toNTTVec w) j)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3_loop]
    unfold_ext; simp; rfl
  · intro i acc hi hacc
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    have e := partialIP_succ (toNTTVec v) (toNTTVec w) i.val hi
    rw [getElem_toNTTVec v _ hi, getElem_toNTTVec w _ hi] at e
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · simpa [hs, partialIP_zero] using hout

-- INTERFACE
@[step] theorem ntt_dot_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3
  unfold_ext
  step with ntt_dot_loop_spec_3 as ⟨ r, hr1, hr2 ⟩
  · exact zero_coeffs_spec
  · exact ⟨hr1, by rw [← partialIP_full]; exact hr2⟩

theorem ntt_mat_mul_loop_spec_3 (A : Mat3) (v : Vec3) (hA : Mat.Bounded q A) (hv : Vec.Bounded q v)
    (iter : core.ops.range.Range Usize) (out : Vec3)
    (hend : iter.end.val = 3) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3_loop iter A v out
      ⦃ r => ∀ j < 3, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v) ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 3#usize)
    (module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3_loop · A v)
    (fun i => do
      let row ← Array.index_usize A i
      module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3 row v)
    (fun j (x : Coeffs) => x.Bounded q ∧
      x.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v))
  · intro iter out
    rw [module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hA.get! i.val hi
    rw [Arr.getElem!_eq A _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_3 (A : Mat3) (v : Vec3)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  unfold module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3
  unfold_ext
  step with ntt_mat_mul_loop_spec_3 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Wychelean.Utils.Linear.Mat.mulVec, Vector.getElem_map, getElem_toNTTVec r j hj,
    getElem_toNTTMat A j hj, (hr j hj).2]

/-! ### Rank 4 -/

theorem vec_add_loop_spec_4 (v w : Vec4) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec4)
    (hend : iter.end.val = 4) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop iter v w out
      ⦃ r => ∀ j < 4, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toPoly q r.val[j]! = (v.val[j]!).toPoly + (w.val[j]!).toPoly ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 4#usize)
    (module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toPoly = (v.val[j]!).toPoly + (w.val[j]!).toPoly)
  · intro iter out
    rw [module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem vec_add_ref_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4
  unfold_ext
  step with vec_add_loop_spec_4 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toPolyVec q r j hj, getElem_toPolyVec q v j hj,
    getElem_toPolyVec q w j hj, (hr j hj).2]

-- INTERFACE
@[step] theorem vec_add_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U4_Add_Vector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  unfold module_lattice.algebra.Vector_BaseField_U4_Add_Vector_BaseField_U4.add_BaseField_U4BaseFieldU4
  exact vec_add_ref_spec_4 v w hv hw

theorem ntt_vec_add_loop_spec_4 (v w : Vec4) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Vec4)
    (hend : iter.end.val = 4) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop iter v w out
      ⦃ r => ∀ j < 4, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = (v.val[j]!).toTq + (w.val[j]!).toTq ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 4#usize)
    (module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop · v w)
    (fun i => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField x y)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = (v.val[j]!).toTq + (w.val[j]!).toTq)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_vec_add_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4
  unfold_ext
  step with ntt_vec_add_loop_spec_4 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_add, getElem_toNTTVec r j hj, getElem_toNTTVec v j hj,
    getElem_toNTTVec w j hj, (hr j hj).2]

theorem ntt_dot_loop_spec_4 (v w : Vec4) (hv : Vec.Bounded q v) (hw : Vec.Bounded q w)
    (iter : core.ops.range.Range Usize) (out : Coeffs)
    (hend : iter.end.val = 4) (hs : iter.start.val = 0) (hout : out.Bounded q ∧ out.toTq = 0) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4_loop iter v w out
      ⦃ r => Coeffs.Bounded q r ∧ Coeffs.toTq r = partialIP (toNTTVec v) (toNTTVec w) 4 ⦄ := by
  apply fold_loop_spec (β := Coeffs) 4
    (module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4_loop · v w)
    (fun i acc => do
      let x ← Array.index_usize v i
      let y ← Array.index_usize w i
      let z ← module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField x y
      module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField acc z)
    (fun j (x : Coeffs) => x.Bounded q ∧ x.toTq = partialIP (toNTTVec v) (toNTTVec w) j)
  · intro iter out
    rw [module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4_loop]
    unfold_ext; simp; rfl
  · intro i acc hi hacc
    have := hv.get! i.val hi
    have := hw.get! i.val hi
    have e := partialIP_succ (toNTTVec v) (toNTTVec w) i.val hi
    rw [getElem_toNTTVec v _ hi, getElem_toNTTVec w _ hi] at e
    rw [Arr.getElem!_eq v _ hi, Arr.getElem!_eq w _ hi] at *
    step*
  · simp [hend]
  · omega
  · simpa [hs, partialIP_zero] using hout

-- INTERFACE
@[step] theorem ntt_dot_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  unfold module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4
  unfold_ext
  step with ntt_dot_loop_spec_4 as ⟨ r, hr1, hr2 ⟩
  · exact zero_coeffs_spec
  · exact ⟨hr1, by rw [← partialIP_full]; exact hr2⟩

theorem ntt_mat_mul_loop_spec_4 (A : Mat4) (v : Vec4) (hA : Mat.Bounded q A) (hv : Vec.Bounded q v)
    (iter : core.ops.range.Range Usize) (out : Vec4)
    (hend : iter.end.val = 4) (hs : iter.start.val = 0) :
    module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4_loop iter A v out
      ⦃ r => ∀ j < 4, Coeffs.Bounded q r.val[j]! ∧
        Coeffs.toTq r.val[j]! = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v) ⦄ := by
  apply map_loop_spec (α := Coeffs) (n := 4#usize)
    (module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4_loop · A v)
    (fun i => do
      let row ← Array.index_usize A i
      module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4 row v)
    (fun j (x : Coeffs) => x.Bounded q ∧
      x.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec (A.val[j]!)) (toNTTVec v))
  · intro iter out
    rw [module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4_loop]
    unfold_ext; simp; rfl
  · intro i hi
    have := hA.get! i.val hi
    rw [Arr.getElem!_eq A _ hi] at *
    step*
  · simp [hend]
  · omega
  · intro j hj; omega

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_4 (A : Mat4) (v : Vec4)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  unfold module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4
  unfold_ext
  step with ntt_mat_mul_loop_spec_4 as ⟨ r, hr ⟩
  refine ⟨Vec.bounded_of fun j hj => (hr j hj).1, ?_⟩
  refine Vector.ext fun j hj => ?_
  rw [Wychelean.Utils.Linear.Mat.mulVec, Vector.getElem_map, getElem_toNTTVec r j hj,
    getElem_toNTTMat A j hj, (hr j hj).2]

end MlKem.Properties
