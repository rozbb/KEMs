import MlKem.Properties.Poly
import Wychelean.KEM.MLKEM.Properties.Loops

/-! # The NTT

Specs of `Ntt for Polynomial` and `NttInverse for NttPolynomial` (Algorithms 9 and 10), and of
their vector versions.

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

namespace NttInternal

/-! ### Reading Rust polynomials -/

theorem toVector_getElem (a : Coeffs) (k : ℕ) (hk : k < 256) :
    (a.toVector q)[k] = toZq (a.val[k]'(by have := a.property; simp_all)) := by
  simp [Coeffs.toVector]

theorem toVector_set (a : Coeffs) (i : Usize) (x : U16) (hi : i.val < 256) :
    Coeffs.toVector q (a.set i x) = (a.toVector q).set i.val (toZq x) hi := by
  ext k hk
  simp only [Coeffs.toVector, Vector.getElem_ofFn, Vector.getElem_set]
  simp only [Array.set_val_eq]
  rw [List.getElem_set]
  split <;> simp_all

theorem bounded_set (a : Coeffs) (i : Usize) (x : U16) (ha : a.Bounded q) (hx : x.val < q) :
    Coeffs.Bounded q (a.set i x) := by
  intro y hy
  simp only [Array.set_val_eq] at hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact ha y h
  · subst h; exact hx

theorem bounded_get (a : Coeffs) (ha : a.Bounded q) (k : ℕ) (hk : k < a.val.length) :
    (a.val[k]).val < q := ha _ (List.getElem_mem hk)

theorem toZq_mod (x : U16) (n : ℕ) (h : x.val = n % 3329) : toZq x = (n : Zq) := by
  simp [toZq, toZMod, h, ZMod.natCast_mod]

theorem toZq_add (x a b : U16) (h : x.val = (a.val + b.val) % 3329) :
    toZq x = toZq a + toZq b := by
  rw [toZq_mod x _ h]; simp [toZq, toZMod]

theorem toZq_sub (x a b : U16) (hb : b.val < 3329) (h : x.val = (a.val + 3329 - b.val) % 3329) :
    toZq x = toZq a - toZq b := by
  rw [toZq_mod x _ h, Nat.cast_sub (by omega)]
  simp [toZq, toZMod]

theorem toZq_mul (x a b : U16) (h : x.val = (a.val * b.val) % 3329) :
    toZq x = toZq a * toZq b := by
  rw [toZq_mod x _ h]; simp [toZq, toZMod]


/-! ### The layers: generic specs of the butterfly loops -/

/-- One forward butterfly at `k` (Algorithm 9, steps 8–10). -/
def fwdBF (len : ℕ) (z : Zq) (v : Vector Zq 256) (k : ℕ) : Vector Zq 256 :=
  if h : k + len < 256 then
    let u := v[k]
    let t := z * v[k + len]
    (v.set (k + len) (u - t)).set k (u + t)
  else v

abbrev Arr := hybrid_array.Array_Elem_BaseField_U256

theorem fwd_inner_spec (LEN : Usize)
    (inner : core.ops.range.Range Usize → Arr → U16 → Result Arr)
    (heq : ∀ iter f zeta, inner iter f zeta = (do
      let (o, iter1) ←
        core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok f
      | some j =>
        let i ← j + LEN
        let ebf ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f i
        let t ←
          module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField
            zeta ebf
        let ebf1 ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f j
        let ebf2 ←
          module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField
            ebf1 t
        let (_, index_mut_Elem_BaseField_usize_U256_back) ←
          hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f i
        let f1 := index_mut_Elem_BaseField_usize_U256_back ebf2
        let ebf3 ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f1 j
        let ebf4 ←
          module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField
            ebf3 t
        let (_, index_mut_Elem_BaseField_usize_U256_back1) ←
          hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f1 j
        let f2 := index_mut_Elem_BaseField_usize_U256_back1 ebf4
        inner iter1 f2 zeta))
    (iter : core.ops.range.Range Usize) (f : Coeffs) (zeta : U16)
    (hz : zeta.val < q) (hf : f.Bounded q) (hLEN : 0 < LEN.val) (hend : iter.end.val + LEN.val ≤ 256) :
    inner iter f zeta ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q =
      (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
        (fwdBF LEN.val (toZq zeta)) (f.toVector q) ⦄ := by
  rw [heq]
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next,
    hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
  by_cases hlt : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    have hs : iter.start.val + LEN.val < 256 := by omega
    step*
    all_goals first
      | (rw [ebf_post]; exact bounded_get f hf _ _)
      | (rw [ebf1_post]; exact bounded_get f hf _ _)
      | (rw [ebf3_post, index_mut_Elem_BaseField_usize_U256_back_post]
         exact bounded_get _ (bounded_set f _ _ hf (by rw [ebf2_post]; exact Nat.mod_lt _ (by decide))) _ _)
      | skip
    have hf1 : Coeffs.Bounded q (index_mut_Elem_BaseField_usize_U256_back ebf2) := by
      rw [index_mut_Elem_BaseField_usize_U256_back_post]
      exact bounded_set f _ _ hf (by rw [ebf2_post]; exact Nat.mod_lt _ (by decide))
    have hf2 : Coeffs.Bounded q (index_mut_Elem_BaseField_usize_U256_back1 ebf4) := by
      rw [index_mut_Elem_BaseField_usize_U256_back1_post]
      exact bounded_set _ _ _ hf1 (by rw [ebf4_post]; exact Nat.mod_lt _ (by decide))
    have hbf : Coeffs.toVector q (index_mut_Elem_BaseField_usize_U256_back1 ebf4) =
        fwdBF LEN.val (toZq zeta) (f.toVector q) iter.start.val := by
      -- the butterfly
      rw [index_mut_Elem_BaseField_usize_U256_back1_post, index_mut_Elem_BaseField_usize_U256_back_post]
      rw [toVector_set _ _ _ (by scalar_tac), toVector_set _ _ _ (by scalar_tac)]
      unfold fwdBF
      rw [dif_pos hs]
      simp only [i_post]
      have hne : iter.start.val ≠ i.val := by scalar_tac
      have e3 : ebf3 = ebf1 := by
        rw [ebf3_post, ebf1_post, index_mut_Elem_BaseField_usize_U256_back_post]
        simp_lists
      have hz2 : toZq t = toZq zeta * (f.toVector q)[iter.start.val + LEN.val] := by
        rw [toZq_mul t zeta ebf t_post, toVector_getElem, ebf_post]
        simp only [i_post]
      have hb1 : toZq ebf1 = (f.toVector q)[iter.start.val] := by
        rw [toVector_getElem, ebf1_post]
      rw [toZq_add ebf4 ebf3 t ebf4_post, e3, toZq_sub ebf2 ebf1 t (by rw [t_post]; exact Nat.mod_lt _ (by decide)) ebf2_post, hz2, hb1]
    apply WP.spec_mono (fwd_inner_spec LEN inner heq iter1 _ zeta hz hf2 hLEN (by rw [hend']; exact hend))
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, ?_⟩
    rw [hr2, hstart', hend']
    rw [show iter.end.val - iter.start.val = (iter.end.val - (iter.start.val + 1)) + 1 by omega,
      List.range'_succ, List.foldl_cons]
    rw [hbf]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst hnone
    simp only [WP.spec_ok]
    refine ⟨hf, ?_⟩
    rw [show iter.end.val - iter.start.val = 0 by omega]
    rfl
termination_by iter.end.val - iter.start.val
decreasing_by scalar_decr_tac


/-! ### The table `ZETA_POW_BITREV` -/

theorem QLL_val' : algebra.BaseField_Field.QLL.val = 3329 := by
  simp [algebra.BaseField_Field.QLL]

theorem zpb_loop0_spec (pow : Std.Array U16 128#usize) (i : Usize) (curr : U64) (hi : i.val ≤ 128)
    (hcurr : curr.val = 17 ^ i.val % 3329)
    (hpow : ∀ j < i.val, pow.val[j]!.val = 17 ^ j % 3329) :
    algebra.ZETA_POW_BITREV_loop0 pow i curr ⦃ r => ∀ j < 128, r.val[j]!.val = 17 ^ j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV_loop0
  simp only [module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField, aeneas_mono.array_index_mut_Elem_BaseField_128, algebra.ZETA_POW_BITREV.ZETA]
  split
  · have hc : curr.val < 3329 := by rw [hcurr]; exact Nat.mod_lt _ (by norm_num)
    step*
    · rw [QLL_val']; decide
    · rw [curr1_post, i4_post, QLL_val', hcurr, i3_post, pow_succ, Nat.mod_mul_mod]
    · have hi2 : i2.val = 17 ^ i.val % 3329 := by
        rw [i2_post, UScalar.cast_val_eq, i1_post, UScalar.val_and]
        rw [show (65535#u64).val = 2^16 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
        simp only [UScalarTy.U16_numBits_eq]
        rw [Nat.mod_mod_of_dvd _ (by norm_num), Nat.mod_eq_of_lt (by omega), hcurr]
      intro j hj
      rw [array_index_mut_Elem_BaseField_128_back_post]
      by_cases hji : j = i.val
      · subst hji; simp_lists [hi2]
      · have h := hpow j (by omega)
        simp_lists at h ⊢; exact h
  · simp only [WP.spec_ok]; intro j hj; exact hpow j (by scalar_tac)
termination_by 128 - i.val
decreasing_by scalar_decr_tac

theorem bitrev_nat (M : ℕ) (hM : M = 2^32 ∨ M = 2^64) : ∀ n < 128, (n >>> 6 % 2 ||| (n >>> 5 % 2) <<< 1 % M ||| (n >>> 4 % 2) <<< 2 % M ||| (n >>> 3 % 2) <<< 3 % M ||| (n >>> 2 % 2) <<< 4 % M ||| (n >>> 1 % 2) <<< 5 % M ||| (n % 2) <<< 6 % M) = Wychelean.bitRev 7 n := by
  rcases hM with rfl | rfl <;> decide

theorem ntt_bitRev7_lt : ∀ n < 128, Wychelean.bitRev 7 n < 128 := by decide

@[step] theorem ntt_bitrev7_spec (x : Usize) (hx : x.val < 128) :
    algebra.ZETA_POW_BITREV.bitrev7 x ⦃ r => r.val = Wychelean.bitRev 7 x.val ⦄ := by
  unfold algebra.ZETA_POW_BITREV.bitrev7
  step* <;> try ((rcases System.Platform.numBits_eq with h | h <;> simp [h]); done)
  simp only [UScalar.val_or, *]
  apply bitrev_nat _ _ _ hx
  rw [Usize.size_def, Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem zpb_loop1_spec (pow pb : Std.Array U16 128#usize) (i : Usize) (hi : i.val ≤ 128)
    (hpow : ∀ j < 128, pow.val[j]!.val = 17 ^ j % 3329)
    (hpb : ∀ j < i.val, pb.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329) :
    algebra.ZETA_POW_BITREV_loop1 pow pb i
      ⦃ r => ∀ j < 128, r.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV_loop1
  simp only [aeneas_mono.array_index_mut_Elem_BaseField_128, aeneas_mono.array_index_Elem_BaseField_128]
  split
  · have := ntt_bitRev7_lt i.val (by scalar_tac)
    step*
    intro j hj
    rw [array_index_mut_Elem_BaseField_128_back_post]
    by_cases hji : j = i.val
    · subst hji
      have h := hpow (Wychelean.bitRev 7 i.val) this
      simp_lists [ebf_post, i1_post] at h ⊢; exact h
    · have h := hpb j (by omega)
      simp_lists at h ⊢; exact h
  · simp only [WP.spec_ok]; intro j hj; exact hpb j (by scalar_tac)
termination_by 128 - i.val
decreasing_by scalar_decr_tac

/-- The twiddle table: `ZETA_POW_BITREV[j] = 17^BitRev₇(j) mod q`. -/
theorem zeta_table_spec :
    algebra.ZETA_POW_BITREV ⦃ r => ∀ j < 128, r.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329 ⦄ := by
  unfold algebra.ZETA_POW_BITREV
  simp only [module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField]
  let* ⟨ pow, hpow ⟩ ← zpb_loop0_spec
  exact zpb_loop1_spec _ _ _ (by simp) hpow (by intro j hj; simp at hj)

/-- Algorithm 9, one block: the twiddle `ζ^BitRev₇(k)`, then the butterflies. -/
def fwdBlk (len : ℕ) (st : Vector Zq 256 × ℕ) (b : ℕ) : Vector Zq 256 × ℕ :=
  ((List.range' (2 * len * b) len).foldl (fwdBF len (ζ ^ Wychelean.bitRev 7 st.2)) st.1, st.2 + 1)

theorem zeta_toZq (a : Std.Array U16 128#usize)
    (ha : ∀ j < 128, a.val[j]!.val = 17 ^ Wychelean.bitRev 7 j % 3329) (k : ℕ) (hk : k < 128) :
    toZq (a.val[k]'(by have := a.property; simp_all)) = ζ ^ Wychelean.bitRev 7 k ∧
      (a.val[k]'(by have := a.property; simp_all)).val < q := by
  have h := ha k hk
  have hk' : k < a.val.length := by have := a.property; simp_all
  rw [getElem!_pos a.val k hk'] at h
  refine ⟨?_, ?_⟩
  · rw [toZq_mod _ _ h]; simp [ζ]
  · rw [h]; exact Nat.mod_lt _ (by decide)

theorem fwd_outer_spec (LEN : Usize)
    (inner : core.ops.range.Range Usize → Arr → U16 → Result Arr)
    (hinner : ∀ (iter : core.ops.range.Range Usize) (f : Coeffs) (zeta : U16),
      zeta.val < q → f.Bounded q → 0 < LEN.val → iter.end.val + LEN.val ≤ 256 →
      inner iter f zeta ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q =
        (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
          (fwdBF LEN.val (toZq zeta)) (f.toVector q) ⦄)
    (outer : core.ops.range.Range Usize → Arr → Usize → Result (Arr × Usize))
    (heq : ∀ iter f k, outer iter f k = (do
      let (o, iter1) ←
        core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok (f, k)
      | some i =>
        let i1 ← i * 2#usize
        let start ← i1 * LEN
        let a ← algebra.ZETA_POW_BITREV
        let zeta ← aeneas_mono.array_index_Elem_BaseField_128 a k
        let k1 ← k + 1#usize
        let i2 ← start + LEN
        let iter2 ←
          core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter
            { start, «end» := i2 }
        let f1 ← inner iter2 f zeta
        outer iter1 f1 k1))
    (iter : core.ops.range.Range Usize) (f : Coeffs) (k : Usize)
    (hf : f.Bounded q) (hLEN : 0 < LEN.val) (hend : iter.end.val * (2 * LEN.val) ≤ 256)
    (hk : k.val + (iter.end.val - iter.start.val) ≤ 128) :
    outer iter f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
        (fwdBlk LEN.val) (f.toVector q, k.val) ⦄ := by
  rw [heq]
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    aeneas_mono.array_index_Elem_BaseField_128]
  by_cases hlt : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    have hb : (iter.start.val + 1) * (2 * LEN.val) ≤ 256 := le_trans (Nat.mul_le_mul_right _ hlt) hend
    have hS : iter.start.val * LEN.val * 2 + LEN.val * 2 ≤ 256 := by ring_nf at hb ⊢; omega
    have hS1 : iter.start.val < 256 := by
      have : iter.start.val * 1 ≤ iter.start.val * LEN.val := Nat.mul_le_mul_left _ hLEN
      omega
    let* ⟨ i1, i1_post ⟩ ← Usize.mul_spec (x := iter.start) (y := 2#usize) (by simp; scalar_tac)
    have hst : i1.val * LEN.val = iter.start.val * LEN.val * 2 := by rw [i1_post]; ring
    let* ⟨ start, start_post ⟩ ← Usize.mul_spec (x := i1) (y := LEN) (by rw [hst]; scalar_tac)
    rw [hst] at start_post
    let* ⟨ a, ha ⟩ ← zeta_table_spec
    let* ⟨ zeta, zeta_post ⟩ ← Array.index_usize_spec
    obtain ⟨hz1, hz2⟩ := zeta_toZq a ha k.val (by omega)
    rw [← zeta_post] at hz1 hz2
    let* ⟨ k1, k1_post ⟩ ← Usize.add_spec
    let* ⟨ i2, i2_post ⟩ ← Usize.add_spec
    let* ⟨ f1, hf1, hv1 ⟩ ← hinner
    apply WP.spec_mono (fwd_outer_spec LEN inner hinner outer heq iter1 f1 k1 hf1 hLEN
      (by rw [hend']; exact hend) (by rw [hend']; omega))
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, ?_⟩
    have hblk : (Coeffs.toVector q f1, k1.val) = fwdBlk LEN.val (f.toVector q, k.val) iter.start.val := by
      unfold fwdBlk
      rw [hv1, k1_post, hz1]
      simp only [i2_post, start_post, Nat.add_sub_cancel_left]
      rw [show iter.start.val * LEN.val * 2 = 2 * LEN.val * iter.start.val by ring]
    rw [hr2, hstart', hend']
    rw [show iter.end.val - iter.start.val = (iter.end.val - (iter.start.val + 1)) + 1 by omega,
      List.range'_succ, List.foldl_cons, ← hblk]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst hnone
    simp only [WP.spec_ok]
    refine ⟨hf, ?_⟩
    rw [show iter.end.val - iter.start.val = 0 by omega]
    rfl
termination_by iter.end.val - iter.start.val
decreasing_by scalar_decr_tac

/-- One inverse butterfly at `k` (Algorithm 10, steps 8–10). -/
def invBF (len : ℕ) (z : Zq) (v : Vector Zq 256) (k : ℕ) : Vector Zq 256 :=
  if h : k + len < 256 then
    let t := v[k]
    let u := v[k + len]
    (v.set k (t + u)).set (k + len) (z * (u - t))
  else v

theorem inv_inner_spec (LEN : Usize)
    (inner : core.ops.range.Range Usize → Arr → U16 → Result Arr)
    (heq : ∀ iter f zeta, inner iter f zeta = (do
      let (o, iter1) ←
        core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok f
      | some j =>
        let t ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f j
        let i ← j + LEN
        let ebf ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f i
        let ebf1 ←
          module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField
            t ebf
        let (_, index_mut_Elem_BaseField_usize_U256_back) ←
          hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f j
        let f1 := index_mut_Elem_BaseField_usize_U256_back ebf1
        let ebf2 ←
          hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f1 i
        let ebf3 ←
          module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField
            ebf2 t
        let ebf4 ←
          module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField
            zeta ebf3
        let (_, index_mut_Elem_BaseField_usize_U256_back1) ←
          hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256
            f1 i
        let f2 := index_mut_Elem_BaseField_usize_U256_back1 ebf4
        inner iter1 f2 zeta))
    (iter : core.ops.range.Range Usize) (f : Coeffs) (zeta : U16)
    (hz : zeta.val < q) (hf : f.Bounded q) (hLEN : 0 < LEN.val) (hend : iter.end.val + LEN.val ≤ 256) :
    inner iter f zeta ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q =
      (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
        (invBF LEN.val (toZq zeta)) (f.toVector q) ⦄ := by
  rw [heq]
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next,
    hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
  by_cases hlt : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    have hs : iter.start.val + LEN.val < 256 := by omega
    step*
    all_goals first
      | (rw [t_post]; exact bounded_get f hf _ _)
      | (rw [ebf_post]; exact bounded_get f hf _ _)
      | (rw [ebf2_post, index_mut_Elem_BaseField_usize_U256_back_post]
         exact bounded_get _ (bounded_set f _ _ hf (by rw [ebf1_post]; exact Nat.mod_lt _ (by decide))) _ _)
      | skip
    have hf1 : Coeffs.Bounded q (index_mut_Elem_BaseField_usize_U256_back ebf1) := by
      rw [index_mut_Elem_BaseField_usize_U256_back_post]
      exact bounded_set f _ _ hf (by rw [ebf1_post]; exact Nat.mod_lt _ (by decide))
    have hf2 : Coeffs.Bounded q (index_mut_Elem_BaseField_usize_U256_back1 ebf4) := by
      rw [index_mut_Elem_BaseField_usize_U256_back1_post]
      exact bounded_set _ _ _ hf1 (by rw [ebf4_post]; exact Nat.mod_lt _ (by decide))
    have hbf : Coeffs.toVector q (index_mut_Elem_BaseField_usize_U256_back1 ebf4) =
        invBF LEN.val (toZq zeta) (f.toVector q) iter.start.val := by
      rw [index_mut_Elem_BaseField_usize_U256_back1_post, index_mut_Elem_BaseField_usize_U256_back_post]
      rw [toVector_set _ _ _ (by scalar_tac), toVector_set _ _ _ (by scalar_tac)]
      unfold invBF
      rw [dif_pos hs]
      simp only [i_post]
      have hne : iter.start.val ≠ i.val := by scalar_tac
      have e2 : ebf2 = ebf := by
        rw [ebf2_post, ebf_post, index_mut_Elem_BaseField_usize_U256_back_post]
        simp_lists
      have hb : toZq ebf = (f.toVector q)[iter.start.val + LEN.val] := by
        rw [toVector_getElem, ebf_post]
        simp only [i_post]
      have ht : toZq t = (f.toVector q)[iter.start.val] := by
        rw [toVector_getElem, t_post]
      rw [toZq_mul ebf4 zeta ebf3 ebf4_post,
        toZq_sub ebf3 ebf2 t (by rw [t_post]; exact bounded_get f hf _ _) ebf3_post, e2,
        toZq_add ebf1 t ebf ebf1_post, hb, ht]
    apply WP.spec_mono (inv_inner_spec LEN inner heq iter1 _ zeta hz hf2 hLEN (by rw [hend']; exact hend))
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, ?_⟩
    rw [hr2, hstart', hend']
    rw [show iter.end.val - iter.start.val = (iter.end.val - (iter.start.val + 1)) + 1 by omega,
      List.range'_succ, List.foldl_cons]
    rw [hbf]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst hnone
    simp only [WP.spec_ok]
    refine ⟨hf, ?_⟩
    rw [show iter.end.val - iter.start.val = 0 by omega]
    rfl
termination_by iter.end.val - iter.start.val
decreasing_by scalar_decr_tac

/-- Algorithm 10, one block: the twiddle `ζ^BitRev₇(k)`, then the butterflies. -/
def invBlk (len : ℕ) (st : Vector Zq 256 × ℕ) (b : ℕ) : Vector Zq 256 × ℕ :=
  ((List.range' (2 * len * b) len).foldl (invBF len (ζ ^ Wychelean.bitRev 7 st.2)) st.1, st.2 - 1)

theorem inv_outer_spec (LEN : Usize)
    (inner : core.ops.range.Range Usize → Arr → U16 → Result Arr)
    (hinner : ∀ (iter : core.ops.range.Range Usize) (f : Coeffs) (zeta : U16),
      zeta.val < q → f.Bounded q → 0 < LEN.val → iter.end.val + LEN.val ≤ 256 →
      inner iter f zeta ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q =
        (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
          (invBF LEN.val (toZq zeta)) (f.toVector q) ⦄)
    (outer : core.ops.range.Range Usize → Arr → Usize → Result (Arr × Usize))
    (heq : ∀ iter f k, outer iter f k = (do
      let (o, iter1) ←
        core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok (f, k)
      | some i =>
        let i1 ← i * 2#usize
        let start ← i1 * LEN
        let a ← algebra.ZETA_POW_BITREV
        let zeta ← aeneas_mono.array_index_Elem_BaseField_128 a k
        let k1 ← k - 1#usize
        let i2 ← start + LEN
        let iter2 ←
          core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter
            { start, «end» := i2 }
        let f1 ← inner iter2 f zeta
        outer iter1 f1 k1))
    (iter : core.ops.range.Range Usize) (f : Coeffs) (k : Usize)
    (hf : f.Bounded q) (hLEN : 0 < LEN.val) (hend : iter.end.val * (2 * LEN.val) ≤ 256)
    (hk : k.val < 128) (hk' : iter.end.val - iter.start.val ≤ k.val) :
    outer iter f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' iter.start.val (iter.end.val - iter.start.val)).foldl
        (invBlk LEN.val) (f.toVector q, k.val) ⦄ := by
  rw [heq]
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    aeneas_mono.array_index_Elem_BaseField_128]
  by_cases hlt : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    have hb : (iter.start.val + 1) * (2 * LEN.val) ≤ 256 := le_trans (Nat.mul_le_mul_right _ hlt) hend
    have hS : iter.start.val * LEN.val * 2 + LEN.val * 2 ≤ 256 := by ring_nf at hb ⊢; omega
    have hS1 : iter.start.val < 256 := by
      have : iter.start.val * 1 ≤ iter.start.val * LEN.val := Nat.mul_le_mul_left _ hLEN
      omega
    let* ⟨ i1, i1_post ⟩ ← Usize.mul_spec (x := iter.start) (y := 2#usize) (by simp; scalar_tac)
    have hst : i1.val * LEN.val = iter.start.val * LEN.val * 2 := by rw [i1_post]; ring
    let* ⟨ start, start_post ⟩ ← Usize.mul_spec (x := i1) (y := LEN) (by rw [hst]; scalar_tac)
    rw [hst] at start_post
    let* ⟨ a, ha ⟩ ← zeta_table_spec
    let* ⟨ zeta, zeta_post ⟩ ← Array.index_usize_spec
    obtain ⟨hz1, hz2⟩ := zeta_toZq a ha k.val hk
    rw [← zeta_post] at hz1 hz2
    let* ⟨ k1, k1_post ⟩ ← Usize.sub_spec
    let* ⟨ i2, i2_post ⟩ ← Usize.add_spec
    let* ⟨ f1, hf1, hv1 ⟩ ← hinner
    apply WP.spec_mono (inv_outer_spec LEN inner hinner outer heq iter1 f1 k1 hf1 hLEN
      (by rw [hend']; exact hend) (by omega) (by rw [hend']; omega))
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, ?_⟩
    have hblk : (Coeffs.toVector q f1, k1.val) = invBlk LEN.val (f.toVector q, k.val) iter.start.val := by
      unfold invBlk
      rw [hv1, k1_post, hz1]
      simp only [i2_post, start_post, Nat.add_sub_cancel_left]
      rw [show iter.start.val * LEN.val * 2 = 2 * LEN.val * iter.start.val by ring]
    rw [hr2, hstart', hend']
    rw [show iter.end.val - iter.start.val = (iter.end.val - (iter.start.val + 1)) + 1 by omega,
      List.range'_succ, List.foldl_cons, ← hblk]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst hnone
    simp only [WP.spec_ok]
    refine ⟨hf, ?_⟩
    rw [show iter.end.val - iter.start.val = 0 by omega]
    rfl
termination_by iter.end.val - iter.start.val
decreasing_by scalar_decr_tac

theorem fwd_layer_128_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 1 ≤ 128) :
    algebra.ntt_layer_128_11281 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 1).foldl (fwdBlk 128) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_128_11281
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 128#usize algebra.ntt_layer_128_11281_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 128#usize algebra.ntt_layer_128_11281_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_128_11281_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_128_11281_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_128_11281_loop0]; rfl) { start := 0#usize, «end» := 1#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_128_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 1 ≤ k.val) :
    algebra.ntt_inverse_layer_128_11281 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 1).foldl (invBlk 128) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_128_11281
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 128#usize algebra.ntt_inverse_layer_128_11281_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 128#usize algebra.ntt_inverse_layer_128_11281_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_128_11281_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_128_11281_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_128_11281_loop0]; rfl) { start := 0#usize, «end» := 1#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_64_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 2 ≤ 128) :
    algebra.ntt_layer_64_2642 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 2).foldl (fwdBlk 64) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_64_2642
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 64#usize algebra.ntt_layer_64_2642_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 64#usize algebra.ntt_layer_64_2642_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_64_2642_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_64_2642_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_64_2642_loop0]; rfl) { start := 0#usize, «end» := 2#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_64_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 2 ≤ k.val) :
    algebra.ntt_inverse_layer_64_2642 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 2).foldl (invBlk 64) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_64_2642
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 64#usize algebra.ntt_inverse_layer_64_2642_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 64#usize algebra.ntt_inverse_layer_64_2642_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_64_2642_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_64_2642_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_64_2642_loop0]; rfl) { start := 0#usize, «end» := 2#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_32_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 4 ≤ 128) :
    algebra.ntt_layer_32_4324 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 4).foldl (fwdBlk 32) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_32_4324
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 32#usize algebra.ntt_layer_32_4324_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 32#usize algebra.ntt_layer_32_4324_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_32_4324_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_32_4324_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_32_4324_loop0]; rfl) { start := 0#usize, «end» := 4#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_32_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 4 ≤ k.val) :
    algebra.ntt_inverse_layer_32_4324 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 4).foldl (invBlk 32) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_32_4324
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 32#usize algebra.ntt_inverse_layer_32_4324_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 32#usize algebra.ntt_inverse_layer_32_4324_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_32_4324_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_32_4324_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_32_4324_loop0]; rfl) { start := 0#usize, «end» := 4#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_16_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 8 ≤ 128) :
    algebra.ntt_layer_16_8168 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 8).foldl (fwdBlk 16) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_16_8168
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 16#usize algebra.ntt_layer_16_8168_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 16#usize algebra.ntt_layer_16_8168_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_16_8168_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_16_8168_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_16_8168_loop0]; rfl) { start := 0#usize, «end» := 8#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_16_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 8 ≤ k.val) :
    algebra.ntt_inverse_layer_16_8168 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 8).foldl (invBlk 16) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_16_8168
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 16#usize algebra.ntt_inverse_layer_16_8168_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 16#usize algebra.ntt_inverse_layer_16_8168_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_16_8168_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_16_8168_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_16_8168_loop0]; rfl) { start := 0#usize, «end» := 8#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_8_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 16 ≤ 128) :
    algebra.ntt_layer_8_16816 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 16).foldl (fwdBlk 8) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_8_16816
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 8#usize algebra.ntt_layer_8_16816_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 8#usize algebra.ntt_layer_8_16816_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_8_16816_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_8_16816_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_8_16816_loop0]; rfl) { start := 0#usize, «end» := 16#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_8_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 16 ≤ k.val) :
    algebra.ntt_inverse_layer_8_16816 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 16).foldl (invBlk 8) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_8_16816
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 8#usize algebra.ntt_inverse_layer_8_16816_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 8#usize algebra.ntt_inverse_layer_8_16816_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_8_16816_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_8_16816_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_8_16816_loop0]; rfl) { start := 0#usize, «end» := 16#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_4_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 32 ≤ 128) :
    algebra.ntt_layer_4_32432 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 32).foldl (fwdBlk 4) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_4_32432
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 4#usize algebra.ntt_layer_4_32432_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 4#usize algebra.ntt_layer_4_32432_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_4_32432_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_4_32432_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_4_32432_loop0]; rfl) { start := 0#usize, «end» := 32#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_4_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 32 ≤ k.val) :
    algebra.ntt_inverse_layer_4_32432 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 32).foldl (invBlk 4) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_4_32432
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 4#usize algebra.ntt_inverse_layer_4_32432_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 4#usize algebra.ntt_inverse_layer_4_32432_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_4_32432_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_4_32432_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_4_32432_loop0]; rfl) { start := 0#usize, «end» := 32#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

theorem fwd_layer_2_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val + 64 ≤ 128) :
    algebra.ntt_layer_2_64264 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 64).foldl (fwdBlk 2) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_layer_2_64264
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (fwd_outer_spec 2#usize algebra.ntt_layer_2_64264_loop0_loop0
    (fun iter f zeta hz hf hL hend => fwd_inner_spec 2#usize algebra.ntt_layer_2_64264_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_layer_2_64264_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_layer_2_64264_loop0 (fun _ _ _ => by rw [algebra.ntt_layer_2_64264_loop0]; rfl) { start := 0#usize, «end» := 64#usize } f k hf (by simp) (by simp) (by simp; omega))
  intro r hr
  simpa using hr

theorem inv_layer_2_spec (f : Coeffs) (k : Usize) (hf : f.Bounded q) (hk : k.val < 128) (hk' : 64 ≤ k.val) :
    algebra.ntt_inverse_layer_2_64264 f k ⦃ (r : Coeffs × Usize) => r.1.Bounded q ∧ (r.1.toVector q, r.2.val) =
      (List.range' 0 64).foldl (invBlk 2) (f.toVector q, k.val) ⦄ := by
  unfold algebra.ntt_inverse_layer_2_64264
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  apply WP.spec_mono (inv_outer_spec 2#usize algebra.ntt_inverse_layer_2_64264_loop0_loop0
    (fun iter f zeta hz hf hL hend => inv_inner_spec 2#usize algebra.ntt_inverse_layer_2_64264_loop0_loop0
      (fun _ _ _ => by rw [algebra.ntt_inverse_layer_2_64264_loop0_loop0]; rfl) iter f zeta hz hf hL hend)
    algebra.ntt_inverse_layer_2_64264_loop0 (fun _ _ _ => by rw [algebra.ntt_inverse_layer_2_64264_loop0]; rfl) { start := 0#usize, «end» := 64#usize } f k hf (by simp) (by simp) hk (by simp; omega))
  intro r hr
  simpa using hr

/-! ### The layers compute the spec's stages -/

theorem forwardStage_eq (st : Vector Zq 256 × ℕ) (s : Fin 7) :
    NTT.forwardStage st s = (List.range' 0 (NTT.blocks s)).foldl (fwdBlk (NTT.len s)) st := by
  unfold NTT.forwardStage
  rw [foldl_range'_eq]
  refine congrArg (fun F => Fin.foldl _ F st) ?_
  funext st b
  unfold NTT.forwardBlock fwdBlk
  rw [foldl_range'_eq]
  refine Prod.ext ?_ rfl
  refine congrArg (fun F => Fin.foldl _ F st.1) ?_
  funext a j
  have := NTT.index_lt s b j
  unfold fwdBF
  rw [dif_pos (by simp only [zero_add, one_mul]; omega)]
  simp only [zero_add, one_mul]

theorem inverseStage_eq (st : Vector Zq 256 × ℕ) (s : Fin 7) :
    NTT.inverseStage st s = (List.range' 0 (NTT.blocks s)).foldl (invBlk (NTT.len s)) st := by
  unfold NTT.inverseStage
  rw [foldl_range'_eq]
  refine congrArg (fun F => Fin.foldl _ F st) ?_
  funext st b
  unfold NTT.inverseBlock invBlk
  rw [foldl_range'_eq]
  refine Prod.ext ?_ rfl
  refine congrArg (fun F => Fin.foldl _ F st.1) ?_
  funext a j
  have := NTT.index_lt s b j
  unfold invBF
  rw [dif_pos (by simp only [zero_add, one_mul]; omega)]
  simp only [zero_add, one_mul]

theorem fwdBlk_foldl_snd (len : ℕ) (l : List ℕ) (st : Vector Zq 256 × ℕ) :
    (l.foldl (fwdBlk len) st).2 = st.2 + l.length := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih]; simp [fwdBlk]; omega

theorem invBlk_foldl_snd (len : ℕ) (l : List ℕ) (st : Vector Zq 256 × ℕ) :
    (l.foldl (invBlk len) st).2 = st.2 - l.length := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih]; simp [invBlk]; omega

theorem forward_eq (v : Vector Zq 256) : NTT.forward v =
    ((List.range' 0 64).foldl (fwdBlk 2) ((List.range' 0 32).foldl (fwdBlk 4)
      ((List.range' 0 16).foldl (fwdBlk 8) ((List.range' 0 8).foldl (fwdBlk 16)
      ((List.range' 0 4).foldl (fwdBlk 32) ((List.range' 0 2).foldl (fwdBlk 64)
      ((List.range' 0 1).foldl (fwdBlk 128) (v, 1)))))))).1 := by
  unfold NTT.forward
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, forwardStage_eq]
  rfl

theorem inverse_eq (v : Vector Zq 256) : NTT.inverse v =
    ((List.range' 0 1).foldl (invBlk 128) ((List.range' 0 2).foldl (invBlk 64)
      ((List.range' 0 4).foldl (invBlk 32) ((List.range' 0 8).foldl (invBlk 16)
      ((List.range' 0 16).foldl (invBlk 8) ((List.range' 0 32).foldl (invBlk 4)
      ((List.range' 0 64).foldl (invBlk 2) (v, 127)))))))).1.map (· * 3303) := by
  unfold NTT.inverse
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, inverseStage_eq]
  rfl

/-! ### Vectors: a loop applying a function to every polynomial -/

theorem map_loop_spec {N : Usize} (g : Coeffs → Result Coeffs) (G : Coeffs → Coeffs → Prop)
    (hg : ∀ a, a.Bounded q → g a ⦃ (r : Coeffs) => r.Bounded q ∧ G a r ⦄)
    (loop : core.ops.range.Range Usize → Std.Array Coeffs N → Std.Array Coeffs N →
      Result (Std.Array Coeffs N))
    (heq : ∀ iter self acc, loop iter self acc = (do
      let (o, iter1) ← core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next iter
      match o with
      | none => ok acc
      | some i =>
        let pbf ← Array.index_usize self i
        let npbf ← g pbf
        let (_, back) ← Array.index_mut_usize acc i
        let acc1 := back npbf
        loop iter1 self acc1))
    (iter : core.ops.range.Range Usize) (self acc : Std.Array Coeffs N)
    (hself : Vec.Bounded q self) (hend : iter.end.val = N.val)
    (hacc : ∀ j < iter.start.val, (acc.val[j]!).Bounded q ∧ G (self.val[j]!) (acc.val[j]!)) :
    loop iter self acc ⦃ r => ∀ j < N.val, (r.val[j]!).Bounded q ∧ G (self.val[j]!) (r.val[j]!) ⦄ := by
  rw [heq]
  simp only [core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next]
  by_cases hlt : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    subst ho
    simp only
    have hlen : iter.start.val < self.val.length := by have := self.property; omega
    let* ⟨ pbf, pbf_post ⟩ ← Array.index_usize_spec
    have hpb : pbf.Bounded q := by
      rw [pbf_post]; exact hself _ (List.getElem_mem _)
    let* ⟨ npbf, h1, h2 ⟩ ← hg
    let* ⟨ x, back, hx, hback ⟩ ← Array.index_mut_usize_spec
    apply WP.spec_mono (map_loop_spec g G hg loop heq iter1 self _ hself (by rw [hend']; exact hend) ?_)
    · exact fun r h => h
    · intro j hj
      rw [hback]
      by_cases hji : j = iter.start.val
      · subst hji
        have e : self.val[iter.start.val]! = pbf := by rw [pbf_post]; simp_lists
        rw [e]
        simp_lists
        exact ⟨h1, h2⟩
      · have := hacc j (by omega)
        simp_lists at this ⊢
        exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    subst hnone
    simp only [WP.spec_ok]
    intro j hj
    exact hacc j (by omega)
termination_by iter.end.val - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_bounded_of {N : Usize} (r : Std.Array Coeffs N)
    (h : ∀ j < N.val, (r.val[j]!).Bounded q) : Vec.Bounded q r := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < N.val := by have := r.property; omega
  have := h j hj'
  rwa [getElem!_pos r.val j hj] at this

end NttInternal

open NttInternal

-- INTERFACE
@[step] theorem ntt_spec (a : Coeffs)
    (ha : a.Bounded q) :
    algebra.Polynomial_BaseField_Ntt.ntt a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Polynomial.NTT a.toPoly ⦄ := by
  unfold algebra.Polynomial_BaseField_Ntt.ntt
  let* ⟨ f1, k1, h1b, h1v ⟩ ← fwd_layer_128_spec
  have hk1 := congrArg Prod.snd h1v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk1
  let* ⟨ f2, k2, h2b, h2v ⟩ ← fwd_layer_64_spec
  have hk2 := congrArg Prod.snd h2v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk2
  let* ⟨ f3, k3, h3b, h3v ⟩ ← fwd_layer_32_spec
  have hk3 := congrArg Prod.snd h3v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk3
  let* ⟨ f4, k4, h4b, h4v ⟩ ← fwd_layer_16_spec
  have hk4 := congrArg Prod.snd h4v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk4
  let* ⟨ f5, k5, h5b, h5v ⟩ ← fwd_layer_8_spec
  have hk5 := congrArg Prod.snd h5v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk5
  let* ⟨ f6, k6, h6b, h6v ⟩ ← fwd_layer_4_spec
  have hk6 := congrArg Prod.snd h6v
  simp only [fwdBlk_foldl_snd, List.length_range'] at hk6
  let* ⟨ f7, k7, h7b, h7v ⟩ ← fwd_layer_2_spec
  simp only [hybrid_array.Array_Elem_BaseField_U256.Insts.CoreConvertIntoNttPolynomial_BaseField.into,
    WP.spec_ok]
  refine ⟨h7b, ?_⟩
  rw [NTT_eq_forward]
  unfold Coeffs.toTq Coeffs.toPoly
  have e1 : (List.range' 0 1).foldl (fwdBlk 128) (a.toVector q, 1) = (Coeffs.toVector q f1, k1.val) := by
    rw [h1v]
  rw [forward_eq, e1, ← h2v, ← h3v, ← h4v, ← h5v, ← h6v, ← h7v]

-- INTERFACE
@[step] theorem ntt_inverse_spec (a : Coeffs)
    (ha : a.Bounded q) :
    algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = Tq.NTTInv a.toTq ⦄ := by
  unfold algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse
  simp only [hybrid_array.Array_Elem_BaseField_U256_Clone.clone_Elem_BaseField_U256Elem_BaseFieldU256,
    bind_ok]
  let* ⟨ f1, k1, h1b, h1v ⟩ ← inv_layer_2_spec
  have hk1 := congrArg Prod.snd h1v
  simp only [invBlk_foldl_snd, List.length_range'] at hk1
  let* ⟨ f2, k2, h2b, h2v ⟩ ← inv_layer_4_spec
  have hk2 := congrArg Prod.snd h2v
  simp only [invBlk_foldl_snd, List.length_range'] at hk2
  let* ⟨ f3, k3, h3b, h3v ⟩ ← inv_layer_8_spec
  have hk3 := congrArg Prod.snd h3v
  simp only [invBlk_foldl_snd, List.length_range'] at hk3
  let* ⟨ f4, k4, h4b, h4v ⟩ ← inv_layer_16_spec
  have hk4 := congrArg Prod.snd h4v
  simp only [invBlk_foldl_snd, List.length_range'] at hk4
  let* ⟨ f5, k5, h5b, h5v ⟩ ← inv_layer_32_spec
  have hk5 := congrArg Prod.snd h5v
  simp only [invBlk_foldl_snd, List.length_range'] at hk5
  let* ⟨ f6, k6, h6b, h6v ⟩ ← inv_layer_64_spec
  have hk6 := congrArg Prod.snd h6v
  simp only [invBlk_foldl_snd, List.length_range'] at hk6
  let* ⟨ f7, k7, h7b, h7v ⟩ ← inv_layer_128_spec
  have hk7 := congrArg Prod.snd h7v
  simp only [invBlk_foldl_snd, List.length_range'] at hk7
  simp only [module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField,
    module_lattice.algebra.Polynomial_BaseField.new_BaseFieldBaseField, bind_ok]
  let* ⟨ r, hrb, hrv ⟩ ← elem_mul_poly_spec
  refine ⟨hrb, ?_⟩
  rw [NTTInv_eq_inverse]
  unfold Coeffs.toTq Coeffs.toPoly
  have e1 : (List.range' 0 64).foldl (invBlk 2) (a.toVector q, 127) = (Coeffs.toVector q f1, k1.val) := by
    rw [h1v]
  rw [inverse_eq, e1, ← h2v, ← h3v, ← h4v, ← h5v, ← h6v, ← h7v, hrv]
  refine congrArg Polynomial.mk ?_
  ext i hi
  simp [toZq, toZMod, mul_comm]

-- INTERFACE
@[step] theorem ntt_vec_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U2_Ntt.ntt_U2U2 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  unfold algebra.Vector_BaseField_U2_Ntt.ntt_U2U2
  simp only [module_lattice.algebra.NttVector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Default.default_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Deref.deref_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 2#usize) algebra.Polynomial_BaseField_Ntt.ntt
    (fun a r => r.toTq = Polynomial.NTT a.toPoly) (fun a ha => ntt_spec a ha)
    algebra.Vector_BaseField_U2_Ntt.ntt_U2U2_loop
    (fun _ _ _ => by rw [algebra.Vector_BaseField_U2_Ntt.ntt_U2U2_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, PolyVector.NTT, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U2_NttInverse.ntt_inverse_U2U2 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  unfold algebra.NttVector_BaseField_U2_NttInverse.ntt_inverse_U2U2
  simp only [module_lattice.algebra.Vector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Default.default_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 2#usize) algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse
    (fun a r => r.toPoly = Tq.NTTInv a.toTq) (fun a ha => ntt_inverse_spec a ha)
    algebra.NttVector_BaseField_U2_NttInverse.ntt_inverse_U2U2_loop
    (fun _ _ _ => by rw [algebra.NttVector_BaseField_U2_NttInverse.ntt_inverse_U2U2_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, NTTVector.NTTInv, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this

-- INTERFACE
@[step] theorem ntt_vec_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U3_Ntt.ntt_U3U3 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  unfold algebra.Vector_BaseField_U3_Ntt.ntt_U3U3
  simp only [module_lattice.algebra.NttVector_BaseField_U3_Default.default_BaseField_U3BaseFieldU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Default.default_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Deref.deref_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 3#usize) algebra.Polynomial_BaseField_Ntt.ntt
    (fun a r => r.toTq = Polynomial.NTT a.toPoly) (fun a ha => ntt_spec a ha)
    algebra.Vector_BaseField_U3_Ntt.ntt_U3U3_loop
    (fun _ _ _ => by rw [algebra.Vector_BaseField_U3_Ntt.ntt_U3U3_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, PolyVector.NTT, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U3_NttInverse.ntt_inverse_U3U3 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  unfold algebra.NttVector_BaseField_U3_NttInverse.ntt_inverse_U3U3
  simp only [module_lattice.algebra.Vector_BaseField_U3_Default.default_BaseField_U3BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Default.default_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 3#usize) algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse
    (fun a r => r.toPoly = Tq.NTTInv a.toTq) (fun a ha => ntt_inverse_spec a ha)
    algebra.NttVector_BaseField_U3_NttInverse.ntt_inverse_U3U3_loop
    (fun _ _ _ => by rw [algebra.NttVector_BaseField_U3_NttInverse.ntt_inverse_U3U3_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, NTTVector.NTTInv, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this

-- INTERFACE
@[step] theorem ntt_vec_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U4_Ntt.ntt_U4U4 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  unfold algebra.Vector_BaseField_U4_Ntt.ntt_U4U4
  simp only [module_lattice.algebra.NttVector_BaseField_U4_Default.default_BaseField_U4BaseFieldU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Default.default_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Deref.deref_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 4#usize) algebra.Polynomial_BaseField_Ntt.ntt
    (fun a r => r.toTq = Polynomial.NTT a.toPoly) (fun a ha => ntt_spec a ha)
    algebra.Vector_BaseField_U4_Ntt.ntt_U4U4_loop
    (fun _ _ _ => by rw [algebra.Vector_BaseField_U4_Ntt.ntt_U4U4_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, PolyVector.NTT, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U4_NttInverse.ntt_inverse_U4U4 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  unfold algebra.NttVector_BaseField_U4_NttInverse.ntt_inverse_U4U4
  simp only [module_lattice.algebra.Vector_BaseField_U4_Default.default_BaseField_U4BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Default.default_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, bind_ok]
  let* ⟨ r, hr ⟩ ← NttInternal.map_loop_spec (N := 4#usize) algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse
    (fun a r => r.toPoly = Tq.NTTInv a.toTq) (fun a ha => ntt_inverse_spec a ha)
    algebra.NttVector_BaseField_U4_NttInverse.ntt_inverse_U4U4_loop
    (fun _ _ _ => by rw [algebra.NttVector_BaseField_U4_NttInverse.ntt_inverse_U4U4_loop]; rfl)
  refine ⟨vec_bounded_of r (fun j hj => (hr j hj).1), ?_⟩
  refine Vector.ext (fun i hi => ?_)
  have := (hr i hi).2
  simp only [toNTTVec, toPolyVec, NTTVector.NTTInv, Vector.getElem_ofFn, Vector.getElem_map]
  simp_lists at this ⊢
  exact this


end MlKem.Properties
