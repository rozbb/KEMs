import MlKem.Properties.Arith

/-! # Compression

Specs of `Compress for Polynomial` and `Compress for Vector` (§4.2.1, Eqs. 4.7 and 4.8).

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements.

The element-level Rust formulas are related to the spec as follows:
* `Compress_d`: the spec's rounding `⌈(2^d/q)·x⌋` is `(2^(d+1)·x + q) / (2q)` (`specC`). The Rust code
  computes `((x·2^d + 1665) · ⌊2^34/q⌋) >> 34` (`rustC`); we check by evaluation in the kernel that the
  two agree for all `x < q` (they do not agree symbolically: the Rust rounding constant `1665` is one
  too large, and the truncated reciprocal compensates for it).
* `Decompress_d`: `⌈(q/2^d)·y⌋ = (2qy + 2^d) / 2^(d+1) = (qy + 2^(d-1)) / 2^d`, which is the Rust
  formula on the nose. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

namespace CompressInternal

/-! ## Arithmetic -/

/-- The Rust compression formula, before masking. -/
def rustC (d x : ℕ) : ℕ := ((x * 2 ^ d + 1665) * 5160669) / 2 ^ 34

/-- The spec's `⌈(2^d/q)·x⌋`, before reduction mod `2^d`. -/
def specC (d x : ℕ) : ℕ := (2 ^ (d + 1) * x + 3329) / 6658

/-- `rustC d x = specC d x` for all `x < n`, as a boolean computation. -/
def checkC (d : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => rustC d n == specC d n && checkC d n

theorem rustC_eq_of_checkC (d n x : ℕ) (h : checkC d n = true) (hx : x < n) :
    rustC d x = specC d x := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkC, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h' | rfl
    · exact ih h.2 h'
    · exact h.1

theorem rat_round_nat_div (x y : ℕ) (hy : y ≠ 0) :
    Wychelean.rat_round ((x : ℚ) / (y : ℚ)) = (((2 * x + y) / (2 * y) : ℕ) : ℤ) := by
  simp only [Wychelean.rat_round]
  have : (x : ℚ) / y + 1 / 2 = ((2 * x + y : ℕ) : ℚ) / ((2 * y : ℕ) : ℚ) := by
    simp; field_simp
  rw [this, Rat.floor_natCast_div_natCast]
  simp

theorem compress_eq (d : ℕ) (hd : 1 ≤ d ∧ d < 12) (x : ℕ) (hx : x < q) :
    Compress d (x : Zq) hd = ((specC d x : ℕ) : ZMod (m d)) := by
  unfold Compress
  rw [ZMod.val_natCast_of_lt hx]
  have : (2 ^ d : ℚ) / (q : ℚ) * (x : ℚ) = ((2 ^ d * x : ℕ) : ℚ) / ((q : ℕ) : ℚ) := by
    push_cast; ring
  rw [this, rat_round_nat_div _ _ (by decide)]
  simp only [Int.cast_natCast, specC]
  congr 2
  rw [pow_succ]; ring_nf

theorem decompress_eq (d : ℕ) (hd : 1 ≤ d ∧ d < 12) (y : ℕ) (hy : y < 2 ^ d) :
    Decompress d (y : ZMod (m d)) hd = (((2 * (q * y) + 2 ^ d) / (2 * 2 ^ d) : ℕ) : Zq) := by
  unfold Decompress
  have hm : m d = 2 ^ d := by simp [m, hd.2]
  have hv : (y : ZMod (m d)).val = y := by
    rw [ZMod.val_natCast_of_lt]; rw [hm]; exact hy
  rw [hv]
  have : (q : ℚ) / (2 ^ d : ℚ) * (y : ℚ) = ((q * y : ℕ) : ℚ) / ((2 ^ d : ℕ) : ℚ) := by
    push_cast; ring
  rw [this, rat_round_nat_div _ _ (by positivity)]
  simp only [Int.cast_natCast]

theorem natCast_mod_m (d : ℕ) (hd : d < 12) (n : ℕ) :
    ((n % 2 ^ d : ℕ) : ZMod (m d)) = (n : ZMod (m d)) := by
  rw [ZMod.natCast_eq_natCast_iff']
  have : m d = 2 ^ d := by simp [m, hd]
  rw [this, Nat.mod_mod]

/-! ## Rust primitives -/

@[simp] theorem QL_val : algebra.BaseField_Field.QL.val = 3329 := by
  simp [algebra.BaseField_Field.QL]

@[step] theorem truncate_u32_u16_spec (x : U32) (h : x.val < 2 ^ 16) :
    module_lattice.truncate.u16_Truncate_u32.truncate x ⦃ r => r.val = x.val ⦄ := by
  unfold module_lattice.truncate.u16_Truncate_u32.truncate
  simp only [lift]
  simp [UScalar.cast_val_eq, core.convert.num.FromU32U16.from_val_eq, core.num.U16.MAX, U16.rMax]
  have := Nat.and_two_pow_sub_one_eq_mod x.val 16
  simp only [show 2 ^ 16 - 1 = 65535 by rfl] at this
  omega

@[step] theorem Q_HALF_spec :
    compress.Elem_BaseField_Compress.compress.Q_HALF ⦃ r => r.val = 1665 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress.Q_HALF
  step* <;> simp_all [U64.max_eq]

theorem range_usize_next_spec (r : core.ops.range.Range Usize) :
    core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next r
    ⦃ (opt : Option Usize) (r' : core.ops.range.Range Usize) =>
      (if r.start.val < r.end.val then
         opt = some r.start ∧ r'.start.val = r.start.val + 1
       else
         opt = none ∧ r'.start = r.start) ∧
      r'.end = r.end ⦄ :=
  core.iter.range.IteratorRange.next_Usize_spec r

/-- The loops `for i in 0..self.0.len() { self.0[i].f() }` over an array, with the per-element
spec `hf`. -/
theorem array_map_loop {α : Type} [Inhabited α] {n : Usize}
    (index_mut : Std.Array α n → Usize → Result (α × (α → Std.Array α n)))
    (hidx : ∀ a i, index_mut a i = Array.index_mut_usize a i)
    (f : α → Result (α × α)) (P : α → Prop) (R : α → α → Prop)
    (hf : ∀ x, P x → f x ⦃ (_r r' : α) => R x r' ⦄)
    (loop : core.ops.range.Range Usize → Std.Array α n → Result (Std.Array α n))
    (heq : ∀ iter a, loop iter a = (do
      let (o, iter1) ← core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok a
      | some i =>
        let (e, back) ← index_mut a i
        let (_, e1) ← f e
        let a1 := back e1
        loop iter1 a1))
    (iter : core.ops.range.Range Usize) (a : Std.Array α n)
    (hend : iter.end.val = n.val) (hle : iter.start.val ≤ n.val)
    (hP : ∀ j, iter.start.val ≤ j → j < n.val → P a.val[j]!) :
    loop iter a ⦃ r => ∀ j, j < n.val →
      (j < iter.start.val → r.val[j]! = a.val[j]!) ∧ (iter.start.val ≤ j → R a.val[j]! r.val[j]!) ⦄ := by
  generalize hk : n.val - iter.start.val = k
  induction k generalizing iter a with
  | zero =>
    rw [heq]
    step with range_usize_next_spec as ⟨o, iter1, h1, h2⟩
    have : ¬ iter.start.val < iter.end.val := by omega
    simp only [this, if_false] at h1
    obtain ⟨ho, _⟩ := h1
    subst ho
    simp only [WP.spec_ok]
    intro j hj
    refine ⟨fun _ => by simp, fun _ => by omega⟩
  | succ k ih =>
    rw [heq]
    step with range_usize_next_spec as ⟨o, iter1, h1, h2⟩
    have hlt : iter.start.val < iter.end.val := by omega
    simp only [hlt, if_true] at h1
    obtain ⟨rfl, h3⟩ := h1
    simp only [hidx]
    have hl : iter.start.val < a.val.length := by simp; omega
    step as ⟨e, back, he, hback⟩
    rw [← getElem!_pos a.val _ hl] at he
    have hPe : P e := by rw [he]; exact hP iter.start.val (le_refl _) (by omega)
    step with hf as ⟨u, e1, he1⟩
    subst he hback
    have hP' : ∀ (j : ℕ), iter1.start.val ≤ j → j < n.val → P (a.set iter.start e1).val[j]! := by
      intro j hj1 hj2
      have : iter.start.val ≠ j := by omega
      simpa [Array.set_val_eq, this] using hP j (by omega) hj2
    have := ih iter1 _ (by rw [h2]; exact hend) (by omega) hP' (by omega)
    apply WP.spec_mono this
    intro r hr j hj
    obtain ⟨hr1, hr2⟩ := hr j hj
    refine ⟨fun hjs => ?_, fun hjs => ?_⟩
    · have : iter.start.val ≠ j := by omega
      simpa [Array.set_val_eq, this] using hr1 (by omega)
    · by_cases hje : j = iter.start.val
      · subst hje
        have := hr1 (by omega)
        have h' : (a.set iter.start e1).val[iter.start.val]! = e1 := by
          simp only [Array.set_val_eq, List.getElem!_eq_getElem?_getD, List.getElem?_set_self hl,
            Option.getD_some]
        rw [this, h']
        exact he1
      · have := hr2 (by omega)
        have hne : iter.start.val ≠ j := Ne.symm hje
        simpa [Array.set_val_eq, hne] using this

theorem coeffs_getElem!_mem (a : Coeffs) (j : ℕ) (hj : j < 256) : a.val[j]! ∈ a.val := by
  have hl : j < a.val.length := by simp; omega
  rw [getElem!_pos a.val j hl]
  exact List.getElem_mem hl

theorem coeffs_bounded_of (a : Coeffs) (B : ℕ) (h : ∀ j < 256, (a.val[j]!).val < B) :
    a.Bounded B := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < 256 := by simpa using hj
  have := h j hj'
  rwa [getElem!_pos a.val j hj] at this

theorem toZMod_getElem (m : ℕ) (a : Coeffs) (i : ℕ) (hi : i < 256) :
    (a.toPoly m)[i] = ((a.val[i]!).val : ZMod m) := by
  have hl : i < a.val.length := by simp; omega
  simp [Coeffs.toPoly, Coeffs.toVector, toZMod, getElem!_pos a.val i hl]

theorem vec_getElem!_mem {n : Usize} (v : Std.Array Coeffs n) (j : ℕ) (hj : j < n.val) :
    v.val[j]! ∈ v.val := by
  have hl : j < v.val.length := by simp; omega
  rw [getElem!_pos v.val j hl]
  exact List.getElem_mem hl

theorem vec_bounded_of {n : Usize} (v : Std.Array Coeffs n) (B : ℕ)
    (h : ∀ j < n.val, (v.val[j]!).Bounded B) : Vec.Bounded B v := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < n.val := by simpa using hj
  have := h j hj'
  rwa [getElem!_pos v.val j hj] at this

theorem toPolyVec_getElem (m : ℕ) {n : Usize} (v : Std.Array Coeffs n) (i : ℕ) (hi : i < n.val) :
    (toPolyVec m v)[i] = (v.val[i]!).toPoly m := by
  have hl : i < v.val.length := by simp; omega
  simp [toPolyVec, getElem!_pos v.val i hl]

end CompressInternal

open CompressInternal

/-! ## `d = 1` -/

namespace CompressInternal

@[simp] theorem DIV_SHIFT_U1U1 : compress.U1_CompressionFactor.DIV_SHIFT_U1U1 = 34#usize := by
  unfold compress.U1_CompressionFactor.DIV_SHIFT_U1U1; rfl

@[step] theorem DIV_MUL_U1U1_spec : compress.U1_CompressionFactor.DIV_MUL_U1U1 ⦃ r => r.val = 5160669 ⦄ := by
  unfold compress.U1_CompressionFactor.DIV_MUL_U1U1
  simp only [DIV_SHIFT_U1U1]
  step* <;> simp_all [U64.size, U64.numBits]

@[step] theorem MASK_U1U1_spec : compress.U1_CompressionFactor.MASK_U1U1 ⦃ r => r.val = 2 ^ 1 - 1 ⦄ := by
  unfold compress.U1_CompressionFactor.MASK_U1U1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1]
  step*

@[step] theorem POW2_HALF_U1U1_spec : compress.U1_CompressionFactor.POW2_HALF_U1U1 ⦃ r => r.val = 2 ^ (1 - 1) ⦄ := by
  unfold compress.U1_CompressionFactor.POW2_HALF_U1U1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1]
  step*

theorem and_mask_1 (n : ℕ) : n &&& 1 = n % 2 :=
  Nat.and_two_pow_sub_one_eq_mod n 1

set_option maxRecDepth 100000 in
theorem checkC_1 : checkC 1 3329 = true := by decide +kernel

theorem elem_compress_spec_1 (x : U16) (hx : x.val < 3329) :
    compress.Elem_BaseField_Compress.compress_U1U1 x
      ⦃ (_r r' : U16) => r'.val = specC 1 x.val % 2 ^ 1 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress_U1U1
  simp only [lift, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, DIV_SHIFT_U1U1]
  have hc' := rustC_eq_of_checkC 1 3329 x.val checkC_1 hx
  have hb : specC 1 x.val < 2 ^ 16 := by unfold specC; omega
  have hX : x.val * 2 < 18446744073709551616 := by omega
  simp only [rustC] at hc'
  step*
  all_goals simp_all [core.convert.num.FromU64U16.from_val_eq, U64.size, U64.numBits, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]

theorem elem_decompress_spec_1 (x : U16) (hx : x.val < 2 ^ 1) :
    compress.Elem_BaseField_Compress.decompress_U1U1 x
      ⦃ (_r r' : U16) => r'.val = (x.val * 3329 + 2 ^ (1 - 1)) / 2 ^ 1 ⦄ := by
  unfold compress.Elem_BaseField_Compress.decompress_U1U1
  simp only [lift, typenum.uint.U1_Unsigned.USIZE_U1UTermB1]
  step*
  all_goals simp_all [core.convert.num.FromU32U16.from_val_eq, Nat.shiftRight_eq_div_pow, U32.max_eq]
  all_goals omega

theorem poly_compress_loop_spec_1 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U1U1_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = specC 1 (a.val[j]!).val % 2 ^ 1 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 3329)
    (fun x r => r.val = specC 1 x.val % 2 ^ 1) elem_compress_spec_1
    compress.Polynomial_BaseField_Compress.compress_U1U1_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.compress_U1U1_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

theorem poly_decompress_loop_spec_1 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded (2 ^ 1)) :
    compress.Polynomial_BaseField_Compress.decompress_U1U1_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = ((a.val[j]!).val * 3329 + 2 ^ (1 - 1)) / 2 ^ 1 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 2 ^ 1)
    (fun x r => r.val = (x.val * 3329 + 2 ^ (1 - 1)) / 2 ^ 1) elem_decompress_spec_1
    compress.Polynomial_BaseField_Compress.decompress_U1U1_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.decompress_U1U1_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

end CompressInternal

-- INTERFACE
@[step] theorem poly_compress_spec_1 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U1U1 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 1) ∧ r'.toPoly (m 1) = Polynomial.Compress 1 a.toPoly ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.compress_U1U1
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_compress_loop_spec_1 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => by rw [hr j hj]; exact Nat.mod_lt _ (by decide)), ?_⟩
  ext i hi
  have hai : (a.val[i]!).val < q := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Compress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [compress_eq _ _ _ hai, hr i hi, natCast_mod_m _ (by decide)]

-- INTERFACE
@[step] theorem poly_decompress_spec_1 (a : Coeffs)
    (ha : a.Bounded (2 ^ 1)) :
    compress.Polynomial_BaseField_Compress.decompress_U1U1 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 1 (a.toPoly (m 1)) ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.decompress_U1U1
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_decompress_loop_spec_1 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => ?_), ?_⟩
  · have := ha _ (coeffs_getElem!_mem a j hj)
    rw [hr j hj]; simp only [q] at *; omega
  ext i hi
  have hai : (a.val[i]!).val < 2 ^ 1 := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Decompress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [decompress_eq _ _ _ hai, hr i hi]
  congr 1
  simp only [q, Nat.reducePow, Nat.reduceSub]
  omega

/-! ## `d = 4` -/

namespace CompressInternal

@[simp] theorem DIV_SHIFT_U4U4 : compress.U4_CompressionFactor.DIV_SHIFT_U4U4 = 34#usize := by
  unfold compress.U4_CompressionFactor.DIV_SHIFT_U4U4; rfl

@[step] theorem DIV_MUL_U4U4_spec : compress.U4_CompressionFactor.DIV_MUL_U4U4 ⦃ r => r.val = 5160669 ⦄ := by
  unfold compress.U4_CompressionFactor.DIV_MUL_U4U4
  simp only [DIV_SHIFT_U4U4]
  step* <;> simp_all [U64.size, U64.numBits]

@[step] theorem MASK_U4U4_spec : compress.U4_CompressionFactor.MASK_U4U4 ⦃ r => r.val = 2 ^ 4 - 1 ⦄ := by
  unfold compress.U4_CompressionFactor.MASK_U4U4
  simp only [typenum.uint.U4_Unsigned.USIZE_U4U2B0]
  step*

@[step] theorem POW2_HALF_U4U4_spec : compress.U4_CompressionFactor.POW2_HALF_U4U4 ⦃ r => r.val = 2 ^ (4 - 1) ⦄ := by
  unfold compress.U4_CompressionFactor.POW2_HALF_U4U4
  simp only [typenum.uint.U4_Unsigned.USIZE_U4U2B0]
  step*

theorem and_mask_4 (n : ℕ) : n &&& 15 = n % 16 :=
  Nat.and_two_pow_sub_one_eq_mod n 4

set_option maxRecDepth 100000 in
theorem checkC_4 : checkC 4 3329 = true := by decide +kernel

theorem elem_compress_spec_4 (x : U16) (hx : x.val < 3329) :
    compress.Elem_BaseField_Compress.compress_U4U4 x
      ⦃ (_r r' : U16) => r'.val = specC 4 x.val % 2 ^ 4 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress_U4U4
  simp only [lift, typenum.uint.U4_Unsigned.USIZE_U4U2B0, DIV_SHIFT_U4U4]
  have hc' := rustC_eq_of_checkC 4 3329 x.val checkC_4 hx
  have hb : specC 4 x.val < 2 ^ 16 := by unfold specC; omega
  have hX : x.val * 16 < 18446744073709551616 := by omega
  simp only [rustC] at hc'
  step*
  all_goals simp_all [core.convert.num.FromU64U16.from_val_eq, U64.size, U64.numBits, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt, and_mask_4]

theorem elem_decompress_spec_4 (x : U16) (hx : x.val < 2 ^ 4) :
    compress.Elem_BaseField_Compress.decompress_U4U4 x
      ⦃ (_r r' : U16) => r'.val = (x.val * 3329 + 2 ^ (4 - 1)) / 2 ^ 4 ⦄ := by
  unfold compress.Elem_BaseField_Compress.decompress_U4U4
  simp only [lift, typenum.uint.U4_Unsigned.USIZE_U4U2B0]
  step*
  all_goals simp_all [core.convert.num.FromU32U16.from_val_eq, Nat.shiftRight_eq_div_pow, U32.max_eq]
  all_goals omega

theorem poly_compress_loop_spec_4 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U4U4_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = specC 4 (a.val[j]!).val % 2 ^ 4 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 3329)
    (fun x r => r.val = specC 4 x.val % 2 ^ 4) elem_compress_spec_4
    compress.Polynomial_BaseField_Compress.compress_U4U4_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.compress_U4U4_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

theorem poly_decompress_loop_spec_4 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded (2 ^ 4)) :
    compress.Polynomial_BaseField_Compress.decompress_U4U4_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = ((a.val[j]!).val * 3329 + 2 ^ (4 - 1)) / 2 ^ 4 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 2 ^ 4)
    (fun x r => r.val = (x.val * 3329 + 2 ^ (4 - 1)) / 2 ^ 4) elem_decompress_spec_4
    compress.Polynomial_BaseField_Compress.decompress_U4U4_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.decompress_U4U4_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

end CompressInternal

-- INTERFACE
@[step] theorem poly_compress_spec_4 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U4U4 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 4) ∧ r'.toPoly (m 4) = Polynomial.Compress 4 a.toPoly ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.compress_U4U4
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_compress_loop_spec_4 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => by rw [hr j hj]; exact Nat.mod_lt _ (by decide)), ?_⟩
  ext i hi
  have hai : (a.val[i]!).val < q := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Compress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [compress_eq _ _ _ hai, hr i hi, natCast_mod_m _ (by decide)]

-- INTERFACE
@[step] theorem poly_decompress_spec_4 (a : Coeffs)
    (ha : a.Bounded (2 ^ 4)) :
    compress.Polynomial_BaseField_Compress.decompress_U4U4 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 4 (a.toPoly (m 4)) ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.decompress_U4U4
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_decompress_loop_spec_4 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => ?_), ?_⟩
  · have := ha _ (coeffs_getElem!_mem a j hj)
    rw [hr j hj]; simp only [q] at *; omega
  ext i hi
  have hai : (a.val[i]!).val < 2 ^ 4 := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Decompress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [decompress_eq _ _ _ hai, hr i hi]
  congr 1
  simp only [q, Nat.reducePow, Nat.reduceSub]
  omega

/-! ## `d = 5` -/

namespace CompressInternal

@[simp] theorem DIV_SHIFT_U5U5 : compress.U5_CompressionFactor.DIV_SHIFT_U5U5 = 34#usize := by
  unfold compress.U5_CompressionFactor.DIV_SHIFT_U5U5; rfl

@[step] theorem DIV_MUL_U5U5_spec : compress.U5_CompressionFactor.DIV_MUL_U5U5 ⦃ r => r.val = 5160669 ⦄ := by
  unfold compress.U5_CompressionFactor.DIV_MUL_U5U5
  simp only [DIV_SHIFT_U5U5]
  step* <;> simp_all [U64.size, U64.numBits]

@[step] theorem MASK_U5U5_spec : compress.U5_CompressionFactor.MASK_U5U5 ⦃ r => r.val = 2 ^ 5 - 1 ⦄ := by
  unfold compress.U5_CompressionFactor.MASK_U5U5
  simp only [typenum.uint.U5_Unsigned.USIZE_U5U2B1]
  step*

@[step] theorem POW2_HALF_U5U5_spec : compress.U5_CompressionFactor.POW2_HALF_U5U5 ⦃ r => r.val = 2 ^ (5 - 1) ⦄ := by
  unfold compress.U5_CompressionFactor.POW2_HALF_U5U5
  simp only [typenum.uint.U5_Unsigned.USIZE_U5U2B1]
  step*

theorem and_mask_5 (n : ℕ) : n &&& 31 = n % 32 :=
  Nat.and_two_pow_sub_one_eq_mod n 5

set_option maxRecDepth 100000 in
theorem checkC_5 : checkC 5 3329 = true := by decide +kernel

theorem elem_compress_spec_5 (x : U16) (hx : x.val < 3329) :
    compress.Elem_BaseField_Compress.compress_U5U5 x
      ⦃ (_r r' : U16) => r'.val = specC 5 x.val % 2 ^ 5 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress_U5U5
  simp only [lift, typenum.uint.U5_Unsigned.USIZE_U5U2B1, DIV_SHIFT_U5U5]
  have hc' := rustC_eq_of_checkC 5 3329 x.val checkC_5 hx
  have hb : specC 5 x.val < 2 ^ 16 := by unfold specC; omega
  have hX : x.val * 32 < 18446744073709551616 := by omega
  simp only [rustC] at hc'
  step*
  all_goals simp_all [core.convert.num.FromU64U16.from_val_eq, U64.size, U64.numBits, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt, and_mask_5]

theorem elem_decompress_spec_5 (x : U16) (hx : x.val < 2 ^ 5) :
    compress.Elem_BaseField_Compress.decompress_U5U5 x
      ⦃ (_r r' : U16) => r'.val = (x.val * 3329 + 2 ^ (5 - 1)) / 2 ^ 5 ⦄ := by
  unfold compress.Elem_BaseField_Compress.decompress_U5U5
  simp only [lift, typenum.uint.U5_Unsigned.USIZE_U5U2B1]
  step*
  all_goals simp_all [core.convert.num.FromU32U16.from_val_eq, Nat.shiftRight_eq_div_pow, U32.max_eq]
  all_goals omega

theorem poly_compress_loop_spec_5 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U5U5_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = specC 5 (a.val[j]!).val % 2 ^ 5 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 3329)
    (fun x r => r.val = specC 5 x.val % 2 ^ 5) elem_compress_spec_5
    compress.Polynomial_BaseField_Compress.compress_U5U5_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.compress_U5U5_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

theorem poly_decompress_loop_spec_5 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded (2 ^ 5)) :
    compress.Polynomial_BaseField_Compress.decompress_U5U5_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = ((a.val[j]!).val * 3329 + 2 ^ (5 - 1)) / 2 ^ 5 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 2 ^ 5)
    (fun x r => r.val = (x.val * 3329 + 2 ^ (5 - 1)) / 2 ^ 5) elem_decompress_spec_5
    compress.Polynomial_BaseField_Compress.decompress_U5U5_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.decompress_U5U5_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

end CompressInternal

-- INTERFACE
@[step] theorem poly_compress_spec_5 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U5U5 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 5) ∧ r'.toPoly (m 5) = Polynomial.Compress 5 a.toPoly ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.compress_U5U5
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_compress_loop_spec_5 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => by rw [hr j hj]; exact Nat.mod_lt _ (by decide)), ?_⟩
  ext i hi
  have hai : (a.val[i]!).val < q := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Compress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [compress_eq _ _ _ hai, hr i hi, natCast_mod_m _ (by decide)]

-- INTERFACE
@[step] theorem poly_decompress_spec_5 (a : Coeffs)
    (ha : a.Bounded (2 ^ 5)) :
    compress.Polynomial_BaseField_Compress.decompress_U5U5 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 5 (a.toPoly (m 5)) ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.decompress_U5U5
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_decompress_loop_spec_5 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => ?_), ?_⟩
  · have := ha _ (coeffs_getElem!_mem a j hj)
    rw [hr j hj]; simp only [q] at *; omega
  ext i hi
  have hai : (a.val[i]!).val < 2 ^ 5 := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Decompress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [decompress_eq _ _ _ hai, hr i hi]
  congr 1
  simp only [q, Nat.reducePow, Nat.reduceSub]
  omega

/-! ## `d = 10` -/

namespace CompressInternal

@[simp] theorem DIV_SHIFT_U10U10 : compress.U10_CompressionFactor.DIV_SHIFT_U10U10 = 34#usize := by
  unfold compress.U10_CompressionFactor.DIV_SHIFT_U10U10; rfl

@[step] theorem DIV_MUL_U10U10_spec : compress.U10_CompressionFactor.DIV_MUL_U10U10 ⦃ r => r.val = 5160669 ⦄ := by
  unfold compress.U10_CompressionFactor.DIV_MUL_U10U10
  simp only [DIV_SHIFT_U10U10]
  step* <;> simp_all [U64.size, U64.numBits]

@[step] theorem MASK_U10U10_spec : compress.U10_CompressionFactor.MASK_U10U10 ⦃ r => r.val = 2 ^ 10 - 1 ⦄ := by
  unfold compress.U10_CompressionFactor.MASK_U10U10
  simp only [typenum.uint.U10_Unsigned.USIZE_U10U5B0]
  step*

@[step] theorem POW2_HALF_U10U10_spec : compress.U10_CompressionFactor.POW2_HALF_U10U10 ⦃ r => r.val = 2 ^ (10 - 1) ⦄ := by
  unfold compress.U10_CompressionFactor.POW2_HALF_U10U10
  simp only [typenum.uint.U10_Unsigned.USIZE_U10U5B0]
  step*

theorem and_mask_10 (n : ℕ) : n &&& 1023 = n % 1024 :=
  Nat.and_two_pow_sub_one_eq_mod n 10

set_option maxRecDepth 100000 in
theorem checkC_10 : checkC 10 3329 = true := by decide +kernel

theorem elem_compress_spec_10 (x : U16) (hx : x.val < 3329) :
    compress.Elem_BaseField_Compress.compress_U10U10 x
      ⦃ (_r r' : U16) => r'.val = specC 10 x.val % 2 ^ 10 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress_U10U10
  simp only [lift, typenum.uint.U10_Unsigned.USIZE_U10U5B0, DIV_SHIFT_U10U10]
  have hc' := rustC_eq_of_checkC 10 3329 x.val checkC_10 hx
  have hb : specC 10 x.val < 2 ^ 16 := by unfold specC; omega
  have hX : x.val * 1024 < 18446744073709551616 := by omega
  simp only [rustC] at hc'
  step*
  all_goals simp_all [core.convert.num.FromU64U16.from_val_eq, U64.size, U64.numBits, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt, and_mask_10]

theorem elem_decompress_spec_10 (x : U16) (hx : x.val < 2 ^ 10) :
    compress.Elem_BaseField_Compress.decompress_U10U10 x
      ⦃ (_r r' : U16) => r'.val = (x.val * 3329 + 2 ^ (10 - 1)) / 2 ^ 10 ⦄ := by
  unfold compress.Elem_BaseField_Compress.decompress_U10U10
  simp only [lift, typenum.uint.U10_Unsigned.USIZE_U10U5B0]
  step*
  all_goals simp_all [core.convert.num.FromU32U16.from_val_eq, Nat.shiftRight_eq_div_pow, U32.max_eq]
  all_goals omega

theorem poly_compress_loop_spec_10 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U10U10_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = specC 10 (a.val[j]!).val % 2 ^ 10 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 3329)
    (fun x r => r.val = specC 10 x.val % 2 ^ 10) elem_compress_spec_10
    compress.Polynomial_BaseField_Compress.compress_U10U10_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.compress_U10U10_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

theorem poly_decompress_loop_spec_10 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded (2 ^ 10)) :
    compress.Polynomial_BaseField_Compress.decompress_U10U10_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = ((a.val[j]!).val * 3329 + 2 ^ (10 - 1)) / 2 ^ 10 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 2 ^ 10)
    (fun x r => r.val = (x.val * 3329 + 2 ^ (10 - 1)) / 2 ^ 10) elem_decompress_spec_10
    compress.Polynomial_BaseField_Compress.decompress_U10U10_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.decompress_U10U10_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

end CompressInternal

-- INTERFACE
@[step] theorem poly_compress_spec_10 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U10U10 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 10) ∧ r'.toPoly (m 10) = Polynomial.Compress 10 a.toPoly ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.compress_U10U10
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_compress_loop_spec_10 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => by rw [hr j hj]; exact Nat.mod_lt _ (by decide)), ?_⟩
  ext i hi
  have hai : (a.val[i]!).val < q := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Compress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [compress_eq _ _ _ hai, hr i hi, natCast_mod_m _ (by decide)]

-- INTERFACE
@[step] theorem poly_decompress_spec_10 (a : Coeffs)
    (ha : a.Bounded (2 ^ 10)) :
    compress.Polynomial_BaseField_Compress.decompress_U10U10 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 10 (a.toPoly (m 10)) ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.decompress_U10U10
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_decompress_loop_spec_10 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => ?_), ?_⟩
  · have := ha _ (coeffs_getElem!_mem a j hj)
    rw [hr j hj]; simp only [q] at *; omega
  ext i hi
  have hai : (a.val[i]!).val < 2 ^ 10 := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Decompress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [decompress_eq _ _ _ hai, hr i hi]
  congr 1
  simp only [q, Nat.reducePow, Nat.reduceSub]
  omega

/-! ## `d = 11` -/

namespace CompressInternal

@[simp] theorem DIV_SHIFT_U11U11 : compress.U11_CompressionFactor.DIV_SHIFT_U11U11 = 34#usize := by
  unfold compress.U11_CompressionFactor.DIV_SHIFT_U11U11; rfl

@[step] theorem DIV_MUL_U11U11_spec : compress.U11_CompressionFactor.DIV_MUL_U11U11 ⦃ r => r.val = 5160669 ⦄ := by
  unfold compress.U11_CompressionFactor.DIV_MUL_U11U11
  simp only [DIV_SHIFT_U11U11]
  step* <;> simp_all [U64.size, U64.numBits]

@[step] theorem MASK_U11U11_spec : compress.U11_CompressionFactor.MASK_U11U11 ⦃ r => r.val = 2 ^ 11 - 1 ⦄ := by
  unfold compress.U11_CompressionFactor.MASK_U11U11
  simp only [typenum.uint.U11_Unsigned.USIZE_U11U5B1]
  step*

@[step] theorem POW2_HALF_U11U11_spec : compress.U11_CompressionFactor.POW2_HALF_U11U11 ⦃ r => r.val = 2 ^ (11 - 1) ⦄ := by
  unfold compress.U11_CompressionFactor.POW2_HALF_U11U11
  simp only [typenum.uint.U11_Unsigned.USIZE_U11U5B1]
  step*

theorem and_mask_11 (n : ℕ) : n &&& 2047 = n % 2048 :=
  Nat.and_two_pow_sub_one_eq_mod n 11

set_option maxRecDepth 100000 in
theorem checkC_11 : checkC 11 3329 = true := by decide +kernel

theorem elem_compress_spec_11 (x : U16) (hx : x.val < 3329) :
    compress.Elem_BaseField_Compress.compress_U11U11 x
      ⦃ (_r r' : U16) => r'.val = specC 11 x.val % 2 ^ 11 ⦄ := by
  unfold compress.Elem_BaseField_Compress.compress_U11U11
  simp only [lift, typenum.uint.U11_Unsigned.USIZE_U11U5B1, DIV_SHIFT_U11U11]
  have hc' := rustC_eq_of_checkC 11 3329 x.val checkC_11 hx
  have hb : specC 11 x.val < 2 ^ 16 := by unfold specC; omega
  have hX : x.val * 2048 < 18446744073709551616 := by omega
  simp only [rustC] at hc'
  step*
  all_goals simp_all [core.convert.num.FromU64U16.from_val_eq, U64.size, U64.numBits, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt, and_mask_11]

theorem elem_decompress_spec_11 (x : U16) (hx : x.val < 2 ^ 11) :
    compress.Elem_BaseField_Compress.decompress_U11U11 x
      ⦃ (_r r' : U16) => r'.val = (x.val * 3329 + 2 ^ (11 - 1)) / 2 ^ 11 ⦄ := by
  unfold compress.Elem_BaseField_Compress.decompress_U11U11
  simp only [lift, typenum.uint.U11_Unsigned.USIZE_U11U5B1]
  step*
  all_goals simp_all [core.convert.num.FromU32U16.from_val_eq, Nat.shiftRight_eq_div_pow, U32.max_eq]
  all_goals omega

theorem poly_compress_loop_spec_11 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U11U11_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = specC 11 (a.val[j]!).val % 2 ^ 11 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 3329)
    (fun x r => r.val = specC 11 x.val % 2 ^ 11) elem_compress_spec_11
    compress.Polynomial_BaseField_Compress.compress_U11U11_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.compress_U11U11_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

theorem poly_decompress_loop_spec_11 (iter : core.ops.range.Range Usize) (a : Coeffs)
    (hs : iter.start.val = 0) (he : iter.end.val = 256) (ha : a.Bounded (2 ^ 11)) :
    compress.Polynomial_BaseField_Compress.decompress_U11U11_loop iter a
      ⦃ r => ∀ j < 256, (r.val[j]!).val = ((a.val[j]!).val * 3329 + 2 ^ (11 - 1)) / 2 ^ 11 ⦄ := by
  have := array_map_loop _ (fun _ _ => rfl) _ (fun x : U16 => x.val < 2 ^ 11)
    (fun x r => r.val = (x.val * 3329 + 2 ^ (11 - 1)) / 2 ^ 11) elem_decompress_spec_11
    compress.Polynomial_BaseField_Compress.decompress_U11U11_loop
    (fun _ _ => by rw [compress.Polynomial_BaseField_Compress.decompress_U11U11_loop]; rfl) iter a
    (by simpa using he) (by simp [hs]) (fun j _ hj => ha _ (coeffs_getElem!_mem a j hj))
  apply WP.spec_mono this
  intro r hr j hj
  exact (hr j hj).2 (by omega)

end CompressInternal

-- INTERFACE
@[step] theorem poly_compress_spec_11 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U11U11 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 11) ∧ r'.toPoly (m 11) = Polynomial.Compress 11 a.toPoly ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.compress_U11U11
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_compress_loop_spec_11 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => by rw [hr j hj]; exact Nat.mod_lt _ (by decide)), ?_⟩
  ext i hi
  have hai : (a.val[i]!).val < q := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Compress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [compress_eq _ _ _ hai, hr i hi, natCast_mod_m _ (by decide)]

-- INTERFACE
@[step] theorem poly_decompress_spec_11 (a : Coeffs)
    (ha : a.Bounded (2 ^ 11)) :
    compress.Polynomial_BaseField_Compress.decompress_U11U11 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 11 (a.toPoly (m 11)) ⦄ := by
  unfold compress.Polynomial_BaseField_Compress.decompress_U11U11
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with poly_decompress_loop_spec_11 as ⟨r, hr⟩
  refine ⟨coeffs_bounded_of r _ (fun j hj => ?_), ?_⟩
  · have := ha _ (coeffs_getElem!_mem a j hj)
    rw [hr j hj]; simp only [q] at *; omega
  ext i hi
  have hai : (a.val[i]!).val < 2 ^ 11 := ha _ (coeffs_getElem!_mem a i hi)
  simp only [Polynomial.Decompress, Polynomial.ofFn, Polynomial.getElem_mk, Vector.getElem_ofFn,
    Fin.getElem_fin, toZMod_getElem _ _ _ hi]
  rw [decompress_eq _ _ _ hai, hr i hi]
  congr 1
  simp only [q, Nat.reducePow, Nat.reduceSub]
  omega

-- INTERFACE
@[step] theorem vec_compress_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U2_Compress.compress_U2_U10U2U10 v
      ⦃ (r r' : Vec2) => r = r' ∧ Vec.Bounded (2 ^ 10) r' ∧ toPolyVec (m 10) r' = PolyVector.Compress (k := k .ML_KEM_512) 10 (toPolyVec q v) ⦄ := by
  unfold compress.Vector_BaseField_U2_Compress.compress_U2_U10U2U10
  simp only [hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded q)
    (fun x r => r.Bounded (2 ^ 10) ∧ r.toPoly (m 10) = Polynomial.Compress 10 x.toPoly)
    (fun x hx => WP.spec_mono (poly_compress_spec_10 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U2_Compress.compress_U2_U10U2U10_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U2_Compress.compress_U2_U10U2U10_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (2#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Compress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2

-- INTERFACE
@[step] theorem vec_decompress_spec_2 (v : Vec2)
    (hv : Vec.Bounded (2 ^ 10) v) :
    compress.Vector_BaseField_U2_Compress.decompress_U2_U10U2U10 v
      ⦃ (r r' : Vec2) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_512) 10 (toPolyVec (m 10) v) ⦄ := by
  unfold compress.Vector_BaseField_U2_Compress.decompress_U2_U10U2U10
  simp only [hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded (2 ^ 10))
    (fun x r => r.Bounded q ∧ r.toPoly = Polynomial.Decompress 10 (x.toPoly (m 10)))
    (fun x hx => WP.spec_mono (poly_decompress_spec_10 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U2_Compress.decompress_U2_U10U2U10_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U2_Compress.decompress_U2_U10U2U10_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (2#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Decompress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2

-- INTERFACE
@[step] theorem vec_compress_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U3_Compress.compress_U3_U10U3U10 v
      ⦃ (r r' : Vec3) => r = r' ∧ Vec.Bounded (2 ^ 10) r' ∧ toPolyVec (m 10) r' = PolyVector.Compress (k := k .ML_KEM_768) 10 (toPolyVec q v) ⦄ := by
  unfold compress.Vector_BaseField_U3_Compress.compress_U3_U10U3U10
  simp only [hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded q)
    (fun x r => r.Bounded (2 ^ 10) ∧ r.toPoly (m 10) = Polynomial.Compress 10 x.toPoly)
    (fun x hx => WP.spec_mono (poly_compress_spec_10 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U3_Compress.compress_U3_U10U3U10_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U3_Compress.compress_U3_U10U3U10_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (3#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Compress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2

-- INTERFACE
@[step] theorem vec_decompress_spec_3 (v : Vec3)
    (hv : Vec.Bounded (2 ^ 10) v) :
    compress.Vector_BaseField_U3_Compress.decompress_U3_U10U3U10 v
      ⦃ (r r' : Vec3) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_768) 10 (toPolyVec (m 10) v) ⦄ := by
  unfold compress.Vector_BaseField_U3_Compress.decompress_U3_U10U3U10
  simp only [hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded (2 ^ 10))
    (fun x r => r.Bounded q ∧ r.toPoly = Polynomial.Decompress 10 (x.toPoly (m 10)))
    (fun x hx => WP.spec_mono (poly_decompress_spec_10 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U3_Compress.decompress_U3_U10U3U10_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U3_Compress.decompress_U3_U10U3U10_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (3#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Decompress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2

-- INTERFACE
@[step] theorem vec_compress_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U4_Compress.compress_U4_U11U4U11 v
      ⦃ (r r' : Vec4) => r = r' ∧ Vec.Bounded (2 ^ 11) r' ∧ toPolyVec (m 11) r' = PolyVector.Compress (k := k .ML_KEM_1024) 11 (toPolyVec q v) ⦄ := by
  unfold compress.Vector_BaseField_U4_Compress.compress_U4_U11U4U11
  simp only [hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded q)
    (fun x r => r.Bounded (2 ^ 11) ∧ r.toPoly (m 11) = Polynomial.Compress 11 x.toPoly)
    (fun x hx => WP.spec_mono (poly_compress_spec_11 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U4_Compress.compress_U4_U11U4U11_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U4_Compress.compress_U4_U11U4U11_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (4#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Compress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2

-- INTERFACE
@[step] theorem vec_decompress_spec_4 (v : Vec4)
    (hv : Vec.Bounded (2 ^ 11) v) :
    compress.Vector_BaseField_U4_Compress.decompress_U4_U11U4U11 v
      ⦃ (r r' : Vec4) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_1024) 11 (toPolyVec (m 11) v) ⦄ := by
  unfold compress.Vector_BaseField_U4_Compress.decompress_U4_U11U4U11
  simp only [hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  have hl := array_map_loop _ (fun _ _ => rfl) _ (fun x : Coeffs => x.Bounded (2 ^ 11))
    (fun x r => r.Bounded q ∧ r.toPoly = Polynomial.Decompress 11 (x.toPoly (m 11)))
    (fun x hx => WP.spec_mono (poly_decompress_spec_11 x hx) (fun p hp => by
      obtain ⟨r, r'⟩ := p; exact hp.2))
    compress.Vector_BaseField_U4_Compress.decompress_U4_U11U4U11_loop
    (fun _ _ => by rw [compress.Vector_BaseField_U4_Compress.decompress_U4_U11U4U11_loop]; rfl) { start := 0#usize, «end» := (Std.Array.to_slice v).len } v
    (by simp) (by simp) (fun j _ hj => hv _ (vec_getElem!_mem v j hj))
  step with hl as ⟨r, hr⟩
  refine ⟨vec_bounded_of r _ (fun j hj => ((hr j hj).2 (by simp)).1), ?_⟩
  apply Vector.ext
  intro i hi
  have hi' : i < (4#usize : Usize).val := by simpa using hi
  simp only [PolyVector.Decompress]
  erw [Vector.getElem_map]
  rw [toPolyVec_getElem _ _ _ hi']
  erw [toPolyVec_getElem _ _ _ hi']
  exact ((hr i hi').2 (by simp)).2


end MlKem.Properties
