import MlKem.Properties.Hash
import MlKem.Properties.Encode
import Wychelean.KEM.MLKEM.Properties.Loops

/-! # Sampling

Specs of `matrix_sample_ntt` (built on `sample_ntt`, Algorithm 7) and of `sample_poly_cbd` and
`sample_poly_vec_cbd` (Algorithm 8).

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

/-! ## Helpers -/

namespace Sample

/-! ### Machine arithmetic -/

theorem usize_size_ge : 2^32 ≤ Usize.size := by
  rw [Usize.size_def, Usize.numBits_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem numBits_ge : 32 ≤ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem shl_small (y n : ℕ) (h : y * 2^n < 2^32) : y <<< n % Usize.size = y * 2^n := by
  have := usize_size_ge
  rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; omega

theorem popc_cast (p : ℕ) (hp : p < 65536) (i1 : U32)
    (h : i1.bv = BitVec.ofNat 32 p &&& 65535#u32.bv) :
    (UScalar.cast .U16 i1).val = p := by
  have : i1.val = p := by
    have h2 : i1.val = i1.bv.toNat := rfl
    rw [h2, h]
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    have : (65535#u32).bv.toNat = 2^16 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [UScalar.cast_val_eq, this]
  simp; omega

/-! ### The `ONES` tables -/

/-- `ONES[k]` for `k = x + (y << B)`: `(popcount x - popcount y) mod q`. -/
def onesVal (B : ℕ) (k : ℕ) : ℕ :=
  (Model.popcount (k % 2^B) + 3329 - Model.popcount (k / 2^B)) % 3329

theorem popcount_lt_8 : ∀ n < 8, Model.popcount n ≤ 3 := by decide

theorem ones2_inner_spec (max : Usize) (out : Std.Array U16 16#usize) (x y : Usize)
    (hmax : max.val = 4) (hx : x.val < 4) (hy : y.val ≤ 4) :
    param.ones_array_U16_2_16U16216_loop0_loop0 max out x y ⦃ r => ∀ k (hk : k < 16),
      (r.val[k]'(by grind)).val = if k % 4 = x.val ∧ y.val ≤ k / 4 then onesVal 2 k else (out.val[k]'(by grind)).val ⦄ := by
  unfold param.ones_array_U16_2_16U16216_loop0_loop0
  simp only [core.num.Usize.count_ones, module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField,
    aeneas_mono.array_index_mut_Elem_BaseField_16]
  split
  · have hpx := popcount_lt_8 x.val (by omega)
    have hpy := popcount_lt_8 y.val (by scalar_tac)
    step as ⟨i1, h1, h1'⟩
    step as ⟨x_ones, hxo⟩
    have hxo' : x_ones.val = Model.popcount x.val := by rw [hxo]; exact popc_cast _ (by omega) _ h1'
    step as ⟨i3, h3, h3'⟩
    step as ⟨y_ones, hyo⟩
    have hyo' : y_ones.val = Model.popcount y.val := by rw [hyo]; exact popc_cast _ (by omega) _ h3'
    step*
    · simp; have := numBits_ge; omega
    · rw [i4_post, shl_small _ _ (by omega)]; scalar_tac
    · simp only [Q_val]; scalar_tac
    · simp only [Q_val] at *; scalar_tac
    · simp only [Q_val]; decide
    · rw [i5_post, i4_post, shl_small _ _ (by omega)]; scalar_tac
    · have h4' : i4.val = 4 * y.val := by rw [i4_post, shl_small _ _ (by omega)]; ring
      rw [r_post k k_post, array_index_mut_Elem_BaseField_16_back_post]
      simp only [Q_val] at *
      by_cases hk : k = i5.val
      · subst hk
        simp [onesVal, i8_post, i7_post, i6_post, hxo', hyo']
        have e1 : i5.val % 4 = x.val := by omega
        have e2 : i5.val / 4 = y.val := by omega
        simp [e1, e2, y1_post]
      · have hne : (out.set i5 i8).val[k]'(by grind) = out.val[k]'(by grind) := by
          simp only [Std.Array.set_val_eq]; simp_lists
        rw [hne]
        by_cases c1 : k % 4 = x.val <;> by_cases c2 : y.val + 1 ≤ k / 4 <;>
          by_cases c3 : y.val ≤ k / 4 <;> simp [c1, c2, c3, y1_post] <;> omega
  · simp only [WP.spec_ok]
    intro k hk
    have : ¬ (y.val ≤ k / 4) := by scalar_tac
    simp [this]
termination_by 4 - y.val
decreasing_by scalar_tac

theorem ones2_outer_spec (max : Usize) (out : Std.Array U16 16#usize) (x : Usize)
    (hmax : max.val = 4) (hx : x.val ≤ 4) :
    param.ones_array_U16_2_16U16216_loop0 max out x ⦃ r => ∀ k (hk : k < 16),
      (r.val[k]'(by grind)).val = if x.val ≤ k % 4 then onesVal 2 k else (out.val[k]'(by grind)).val ⦄ := by
  unfold param.ones_array_U16_2_16U16216_loop0
  split
  · step with ones2_inner_spec as ⟨out1, h1⟩
    step*
    rw [r_post k k_post, h1 k k_post]
    by_cases c1 : k % 4 = x.val <;> by_cases c2 : x.val + 1 ≤ k % 4 <;>
      by_cases c3 : x.val ≤ k % 4 <;> simp [c1, c2, c3, x1_post] <;> omega
  · simp only [WP.spec_ok]
    intro k hk
    have : ¬ (x.val ≤ k % 4) := by scalar_tac
    simp [this]
termination_by 4 - x.val
decreasing_by scalar_tac

theorem ones2_spec :
    param.U2_CbdSamplingSize.ONES ⦃ r => ∀ k (hk : k < 16), (r.val[k]'(by grind)).val = onesVal 2 k ⦄ := by
  unfold param.U2_CbdSamplingSize.ONES param.ones_array_U16_2_16U16216
  simp only [module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField]
  step as ⟨max, hmax⟩
  · simp; have := numBits_ge; omega
  step with ones2_outer_spec as ⟨out1, h1⟩
  · rw [hmax, shl_small _ _ (by decide)]; rfl
  intro k hk; rw [h1 k hk]; simp

theorem ones3_inner_spec (max : Usize) (out : Std.Array U16 64#usize) (x y : Usize)
    (hmax : max.val = 8) (hx : x.val < 8) (hy : y.val ≤ 8) :
    param.ones_array_U64_3_64U64364_loop0_loop0 max out x y ⦃ r => ∀ k (hk : k < 64),
      (r.val[k]'(by grind)).val = if k % 8 = x.val ∧ y.val ≤ k / 8 then onesVal 3 k else (out.val[k]'(by grind)).val ⦄ := by
  unfold param.ones_array_U64_3_64U64364_loop0_loop0
  simp only [core.num.Usize.count_ones, module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField,
    aeneas_mono.array_index_mut_Elem_BaseField_64]
  split
  · have hpx := popcount_lt_8 x.val (by omega)
    have hpy := popcount_lt_8 y.val (by scalar_tac)
    step as ⟨i1, h1, h1'⟩
    step as ⟨x_ones, hxo⟩
    have hxo' : x_ones.val = Model.popcount x.val := by rw [hxo]; exact popc_cast _ (by omega) _ h1'
    step as ⟨i3, h3, h3'⟩
    step as ⟨y_ones, hyo⟩
    have hyo' : y_ones.val = Model.popcount y.val := by rw [hyo]; exact popc_cast _ (by omega) _ h3'
    step*
    · simp; have := numBits_ge; omega
    · rw [i4_post, shl_small _ _ (by omega)]; scalar_tac
    · simp only [Q_val]; scalar_tac
    · simp only [Q_val] at *; scalar_tac
    · simp only [Q_val]; decide
    · rw [i5_post, i4_post, shl_small _ _ (by omega)]; scalar_tac
    · have h4' : i4.val = 8 * y.val := by rw [i4_post, shl_small _ _ (by omega)]; ring
      rw [r_post k k_post, array_index_mut_Elem_BaseField_64_back_post]
      simp only [Q_val] at *
      by_cases hk : k = i5.val
      · subst hk
        simp [onesVal, i8_post, i7_post, i6_post, hxo', hyo']
        have e1 : i5.val % 8 = x.val := by omega
        have e2 : i5.val / 8 = y.val := by omega
        simp [e1, e2, y1_post]
      · have hne : (out.set i5 i8).val[k]'(by grind) = out.val[k]'(by grind) := by
          simp only [Std.Array.set_val_eq]; simp_lists
        rw [hne]
        by_cases c1 : k % 8 = x.val <;> by_cases c2 : y.val + 1 ≤ k / 8 <;>
          by_cases c3 : y.val ≤ k / 8 <;> simp [c1, c2, c3, y1_post] <;> omega
  · simp only [WP.spec_ok]
    intro k hk
    have : ¬ (y.val ≤ k / 8) := by scalar_tac
    simp [this]
termination_by 8 - y.val
decreasing_by scalar_tac

theorem ones3_outer_spec (max : Usize) (out : Std.Array U16 64#usize) (x : Usize)
    (hmax : max.val = 8) (hx : x.val ≤ 8) :
    param.ones_array_U64_3_64U64364_loop0 max out x ⦃ r => ∀ k (hk : k < 64),
      (r.val[k]'(by grind)).val = if x.val ≤ k % 8 then onesVal 3 k else (out.val[k]'(by grind)).val ⦄ := by
  unfold param.ones_array_U64_3_64U64364_loop0
  split
  · step with ones3_inner_spec as ⟨out1, h1⟩
    step*
    rw [r_post k k_post, h1 k k_post]
    by_cases c1 : k % 8 = x.val <;> by_cases c2 : x.val + 1 ≤ k % 8 <;>
      by_cases c3 : x.val ≤ k % 8 <;> simp [c1, c2, c3, x1_post] <;> omega
  · simp only [WP.spec_ok]
    intro k hk
    have : ¬ (x.val ≤ k % 8) := by scalar_tac
    simp [this]
termination_by 8 - x.val
decreasing_by scalar_tac

theorem ones3_spec :
    param.U3_CbdSamplingSize.ONES ⦃ r => ∀ k (hk : k < 64), (r.val[k]'(by grind)).val = onesVal 3 k ⦄ := by
  unfold param.U3_CbdSamplingSize.ONES param.ones_array_U64_3_64U64364
  simp only [module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField]
  step as ⟨max, hmax⟩
  · simp; have := numBits_ge; omega
  step with ones3_outer_spec as ⟨out1, h1⟩
  · rw [hmax, shl_small _ _ (by decide)]; rfl
  intro k hk; rw [h1 k hk]; simp

/-! ### Closed forms of the spec's loops -/

theorem foldl_set_ne {α : Type} {n : ℕ} {L : List ℕ} (xs : List {a // a ∈ L})
    (F : {a // a ∈ L} → α) (hp : ∀ x : {a // a ∈ L}, x.1 < n) (v : Vector α n) (k : ℕ) (hk : k < n)
    (hne : ∀ y ∈ xs, y.1 ≠ k) :
    (xs.foldl (fun b x => b.set x.1 (F x) (hp x)) v)[k] = v[k] := by
  induction xs generalizing v with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun z hz => hne z (List.mem_cons_of_mem _ hz))]
    exact Vector.getElem_set_ne _ _ (hne y (List.mem_cons_self ..))

theorem foldl_set_mem {α : Type} {n : ℕ} {L : List ℕ} (xs : List {a // a ∈ L})
    (F : {a // a ∈ L} → α) (hp : ∀ x : {a // a ∈ L}, x.1 < n) (v : Vector α n) (x : {a // a ∈ L})
    (hx : x ∈ xs) :
    (xs.foldl (fun b x => b.set x.1 (F x) (hp x)) v)[x.1]'(hp x) = F x := by
  induction xs generalizing v with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases h : x ∈ ys
    · exact ih _ h
    · have hxy : x = y := by simpa [h] using hx
      subst hxy
      rw [foldl_set_ne _ _ _ _ _ _ (fun z hz hzx => h (by rwa [← Subtype.ext hzx]))]
      simp

/-- Bit `k` of a byte string (`false` out of range). -/
def bitAt {n : ℕ} (B : Wychelean.ByteVec n) (k : ℕ) : Bool :=
  if h : k < 8 * n then (Wychelean.bytesToBits B)[k] else false

theorem bytesToBits_eq_bitAt {n : ℕ} (B : Wychelean.ByteVec n) (k : ℕ) (h : k < 8 * n) :
    (Wychelean.bytesToBits B)[k] = bitAt B k := by simp [bitAt, h]

theorem SamplePolyCBD_coeff {η : Η} (B : Wychelean.ByteVec (64 * η)) (i : ℕ) (hi : i < 256) :
    (SamplePolyCBD B).coeffs[i] =
      ((∑ j : Fin η, (bitAt B (2 * i * η + j)).toNat : ℕ) : Zq) -
      ((∑ j : Fin η, (bitAt B (2 * i * η + η + j)).toNat : ℕ) : Zq) := by
  unfold SamplePolyCBD
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl, pure_bind,
    Id.run_pure]
  have hmem : i ∈ List.range' 0 [:256].size := by simp [Std.Legacy.Range.size]; omega
  rw [foldl_set_mem (L := List.range' 0 [:256].size) _ _ _ _ ⟨i, hmem⟩ (List.mem_attach _ _)]
  simp only [bytesToBits_eq_bitAt]

theorem ByteDecode_coeff {d : ℕ} (B : Wychelean.ByteVec (32 * d)) (hd : 1 ≤ d ∧ d ≤ 12) (i : ℕ)
    (hi : i < 256) :
    (ByteDecode B hd)[i] = ((∑ j : Fin d, (bitAt B (i * d + j)).toNat * 2 ^ j.val : ℕ) : ZMod (m d)) := by
  unfold ByteDecode
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl, pure_bind,
    Id.run_pure]
  have hmem : i ∈ List.range' 0 [:256].size := by simp [Std.Legacy.Range.size]; omega
  rw [foldl_set_mem (L := List.range' 0 [:256].size) _ _ _ _ ⟨i, hmem⟩ (List.mem_attach _ _)]
  simp only [bytesToBits_eq_bitAt]
  push_cast; rfl

/-! ### Iterators -/

@[step] theorem range_next_spec (r : core.ops.range.Range Usize) :
    core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next r
    ⦃ (opt : Option Usize) (r' : core.ops.range.Range Usize) =>
      (if r.start.val < r.end.val then
         opt = some r.start ∧ r'.start.val = r.start.val + 1
       else
         opt = none ∧ r'.start = r.start) ∧
      r'.end = r.end ⦄ :=
  core.iter.range.IteratorRange.next_Usize_spec r

/-! ### `sample_poly_cbd` -/

theorem cbd2_loop_spec (iter : core.ops.range.Range Usize) (a : Std.Array U16 256#usize)
    (hend : iter.end.val = 256) (hstart : iter.start.val ≤ 256)
    (hb : ∀ k (hk : k < 256), iter.start.val ≤ k → (a.val[k]'(by grind)).val < 16) :
    algebra.sample_poly_cbd_U2U2_loop iter a ⦃ r => ∀ k (hk : k < 256),
      (r.val[k]'(by grind)).val = if iter.start.val ≤ k then onesVal 2 (a.val[k]'(by grind)).val
        else (a.val[k]'(by grind)).val ⦄ := by
  unfold algebra.sample_poly_cbd_U2U2_loop
  simp only [hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U16_Index_usize.index_Elem_BaseField_usize_U16Elem_BaseFieldUsizeU16,
    hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
  step*
  step with ones2_spec as ⟨ones, hones⟩
  have hs : iter.start.val < 256 := by
    split_ifs at o_post <;> simp_all
  have hi : i = iter.start := by split_ifs at o_post <;> simp_all
  have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
  subst hi
  step*
  · intro k hk hk'
    rw [index_mut_Elem_BaseField_usize_U256_back_post]
    simp only [Std.Array.set_val_eq]; simp_lists
    exact hb k hk (by omega)
  · rw [r_post k k_post, index_mut_Elem_BaseField_usize_U256_back_post]
    have hlt := hb _ hs (le_refl _)
    by_cases hk : k = iter.start.val
    · subst hk
      simp only [Std.Array.set_val_eq]; simp_lists
      simp [ebf1_post, i1_post, ebf_post]
      have : ¬ (iter1.start.val ≤ iter.start.val) := by omega
      simp only [this, if_false]
      exact hones _ hlt
    · simp only [Std.Array.set_val_eq]; simp_lists
      by_cases c : iter.start.val ≤ k <;> by_cases c' : iter.start.val + 1 ≤ k <;> simp [c, c', h1s] <;> omega
termination_by 256 - iter.start.val
decreasing_by scalar_tac

theorem poly_getElem_eq_coeffs {m : ℕ} (f : Wychelean.KEM.MLKEM.Polynomial m) (i : ℕ) (h : i < 256) :
    f[i] = f.coeffs[i] := rfl

theorem cast_onesVal (p1 p2 : ℕ) (h : p2 ≤ 3329) :
    (((p1 + 3329 - p2) % 3329 : ℕ) : Zq) = (p1 : Zq) - (p2 : Zq) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega)]
  push_cast
  simp

theorem cbd2_val (b0 b1 b2 b3 : Bool) :
    Model.popcount ((b0.toNat * 1 + b1.toNat * 2 + b2.toNat * 4 + b3.toNat * 8) % 2^2) = b0.toNat + b1.toNat ∧
    Model.popcount ((b0.toNat * 1 + b1.toNat * 2 + b2.toNat * 4 + b3.toNat * 8) / 2^2) = b2.toNat + b3.toNat := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem SamplePolyCBD_coeff_2 (B : Wychelean.ByteVec (64 * η₂)) (i : ℕ) (hi : i < 256) :
    (SamplePolyCBD B).coeffs[i] =
      (((bitAt B (4 * i)).toNat + (bitAt B (4 * i + 1)).toNat : ℕ) : Zq) -
      (((bitAt B (4 * i + 2)).toNat + (bitAt B (4 * i + 3)).toNat : ℕ) : Zq) := by
  rw [SamplePolyCBD_coeff B i hi]
  simp only [Fin.sum_univ_eq_sum_range (fun j => (bitAt B (2 * i * ↑η₂ + j)).toNat),
    Fin.sum_univ_eq_sum_range (fun j => (bitAt B (2 * i * ↑η₂ + ↑η₂ + j)).toNat)]
  have h2 : (η₂ : ℕ) = 2 := rfl
  simp only [h2, Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

theorem cbd3_loop_spec (iter : core.ops.range.Range Usize) (a : Std.Array U16 256#usize)
    (hend : iter.end.val = 256) (hstart : iter.start.val ≤ 256)
    (hb : ∀ k (hk : k < 256), iter.start.val ≤ k → (a.val[k]'(by grind)).val < 64) :
    algebra.sample_poly_cbd_U3U3_loop iter a ⦃ r => ∀ k (hk : k < 256),
      (r.val[k]'(by grind)).val = if iter.start.val ≤ k then onesVal 3 (a.val[k]'(by grind)).val
        else (a.val[k]'(by grind)).val ⦄ := by
  unfold algebra.sample_poly_cbd_U3U3_loop
  simp only [hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
    hybrid_array.Array_Elem_BaseField_U64_Index_usize.index_Elem_BaseField_usize_U64Elem_BaseFieldUsizeU64,
    hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
  step*
  step with ones3_spec as ⟨ones, hones⟩
  have hs : iter.start.val < 256 := by
    split_ifs at o_post <;> simp_all
  have hi : i = iter.start := by split_ifs at o_post <;> simp_all
  have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
  subst hi
  step*
  · intro k hk hk'
    rw [index_mut_Elem_BaseField_usize_U256_back_post]
    simp only [Std.Array.set_val_eq]; simp_lists
    exact hb k hk (by omega)
  · rw [r_post k k_post, index_mut_Elem_BaseField_usize_U256_back_post]
    have hlt := hb _ hs (le_refl _)
    by_cases hk : k = iter.start.val
    · subst hk
      simp only [Std.Array.set_val_eq]; simp_lists
      simp [ebf1_post, i1_post, ebf_post]
      have : ¬ (iter1.start.val ≤ iter.start.val) := by omega
      simp only [this, if_false]
      exact hones _ hlt
    · simp only [Std.Array.set_val_eq]; simp_lists
      by_cases c : iter.start.val ≤ k <;> by_cases c' : iter.start.val + 1 ≤ k <;> simp [c, c', h1s] <;> omega
termination_by 256 - iter.start.val
decreasing_by scalar_tac


theorem cbd3_val (b0 b1 b2 b3 b4 b5 : Bool) :
    Model.popcount ((b0.toNat * 1 + b1.toNat * 2 + b2.toNat * 4 + b3.toNat * 8 + b4.toNat * 16 + b5.toNat * 32) % 2^3) =
      b0.toNat + b1.toNat + b2.toNat ∧
    Model.popcount ((b0.toNat * 1 + b1.toNat * 2 + b2.toNat * 4 + b3.toNat * 8 + b4.toNat * 16 + b5.toNat * 32) / 2^3) =
      b3.toNat + b4.toNat + b5.toNat := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem SamplePolyCBD_coeff_3 (B : Wychelean.ByteVec (64 * η₁ .ML_KEM_512)) (i : ℕ) (hi : i < 256) :
    (SamplePolyCBD B).coeffs[i] =
      (((bitAt B (6 * i)).toNat + (bitAt B (6 * i + 1)).toNat + (bitAt B (6 * i + 2)).toNat : ℕ) : Zq) -
      (((bitAt B (6 * i + 3)).toNat + (bitAt B (6 * i + 4)).toNat + (bitAt B (6 * i + 5)).toNat : ℕ) : Zq) := by
  rw [SamplePolyCBD_coeff B i hi]
  simp only [Fin.sum_univ_eq_sum_range (fun j => (bitAt B (2 * i * ↑(η₁ .ML_KEM_512) + j)).toNat),
    Fin.sum_univ_eq_sum_range (fun j => (bitAt B (2 * i * ↑(η₁ .ML_KEM_512) + ↑(η₁ .ML_KEM_512) + j)).toNat)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

/-! ### `sample_poly_vec_cbd` -/

theorem truncate_u8_spec (x : Usize) (h : x.val < 256) :
    module_lattice.truncate.u8_Truncate_usize.truncate x ⦃ r => r.val = x.val ⦄ := by
  unfold module_lattice.truncate.u8_Truncate_usize.truncate
  simp only [lift, Std.bind_ok, WP.spec_ok]
  rw [UScalar.cast_val_eq, UScalar.val_and, core.convert.num.FromUsizeU8.from_val_eq]
  have : (core.num.U8.MAX).val = 2^8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem toByte_eq_ofNat (x : U8) (n : ℕ) (h : x.val = n) : toByte x = UInt8.ofNat n := by
  unfold toByte
  apply UInt8.toNat_inj.mp
  have hx : x.bv.toNat = n := h
  have : n < 256 := by have := x.hBounds; simp at this; omega
  simp [hx]
  omega

/-! ### `sample_ntt`: the spec side -/

/-- Run a loop body for at most `n` iterations. -/
def runN {β : Type} (F : β → ForInStep β) : ℕ → β → Option β
  | 0, _ => none
  | n + 1, b => match F b with
    | .done b' => some b'
    | .yield b' => runN F n b'

theorem loop_forIn_eq {β : Type} (f : Unit → β → Id (ForInStep β)) (F : β → ForInStep β)
    (hF : ∀ b, f () b = F b) (n : ℕ) (b b' : β) (h : runN F n b = some b') :
    forIn Lean.Loop.mk b f = (pure b' : Id β) := by
  induction n generalizing b with
  | zero => simp [runN] at h
  | succ n ih =>
    rw [show forIn Lean.Loop.mk b f = Lean.Loop.forIn Lean.Loop.mk b f from rfl,
      Lean.Loop.forIn_eq_of_monadTail, hF]
    simp only [runN] at h
    cases hFb : F b with
    | done b'' => rw [hFb] at h; simp at h; subst h; rfl
    | yield b'' => rw [hFb] at h; exact ih _ h

abbrev XofState := Wychelean.Hashes.SHA3.Incremental.sponge.state (Wychelean.Hashes.SHA3.Internal.b - 256)

/-- One iteration of Algorithm 7 on the three squeezed bytes `C`. -/
def nttStep (C : Wychelean.ByteVec 3) (j : ℕ) (a : Vector Zq 256) : ℕ × Vector Zq 256 :=
  let d₁ := C[0].toNat + 256 * (C[1].toNat % 16)
  let d₂ := C[1].toNat / 16 + 16 * C[2].toNat
  let p : ℕ × Vector Zq 256 := if h : d₁ < q ∧ j < 256 then (j + 1, a.set j (d₁ : Zq) h.2) else (j, a)
  if h : d₂ < q ∧ p.1 < 256 then (p.1 + 1, p.2.set p.1 (d₂ : Zq) h.2) else p

def nttF (s : MProd XofState (MProd ℕ (Vector Zq 256))) : ForInStep (MProd XofState (MProd ℕ (Vector Zq 256))) :=
  if s.2.1 < 256 then
    let (ctx', C) := XOF.Squeeze s.1 3
    let p := nttStep C s.2.1 s.2.2
    .yield ⟨ctx', p.1, p.2⟩
  else .done s

theorem SampleNTT_eq (B : Wychelean.ByteVec (seedLen + 2)) (n : ℕ) (s' : MProd XofState (MProd ℕ (Vector Zq 256)))
    (h : runN nttF n ⟨XOF.Finalize (XOF.Absorb XOF.Init B), 0, Vector.replicate 256 0⟩ = some s') :
    SampleNTT B = ⟨s'.2.2⟩ := by
  unfold SampleNTT
  dsimp only
  rw [loop_forIn_eq _ nttF _ n _ s' h]
  · rfl
  · intro b
    obtain ⟨ctx, j, a⟩ := b
    simp only [nttF, nttStep]
    generalize XOF.Squeeze ctx 3 = p
    obtain ⟨ctx', C⟩ := p
    dsimp only
    by_cases hj : j < 256
    · by_cases h1 : C[0].toNat + 256 * (C[1].toNat % 16) < q <;>
      by_cases h2 : C[1].toNat / 16 + 16 * C[2].toNat < q <;>
      by_cases h3 : j + 1 < 256 <;> simp [hj, h1, h2, h3] <;> rfl
    · simp [hj]; rfl


theorem squeeze_zero_state (ctx : XofState) : (XOF.Squeeze ctx 0).1 = ctx := by
  have := Wychelean.Hashes.SHA3.SHAKE128.squeeze_chunks ctx []
  simpa [XOF.Squeeze] using this.symm

theorem inv_step (ctx : XofState) (data : List U8) (s : ℕ) (hs : s + 3 ≤ 96)
    (hL : (data.drop s).map toByte = (XOF.Squeeze ctx (96 - s)).2.toList) :
    (∀ t (ht : t < 3) (hd : s + t < data.length), toByte (data[s + t]'hd) = (XOF.Squeeze ctx 3).2[t]) ∧
    (data.drop (s + 3)).map toByte = (XOF.Squeeze (XOF.Squeeze ctx 3).1 (96 - (s + 3))).2.toList ∧
    (XOF.Squeeze (XOF.Squeeze ctx 3).1 (96 - (s + 3))).1 = (XOF.Squeeze ctx (96 - s)).1 := by
  have hsplit := Wychelean.Hashes.SHA3.SHAKE128.squeeze_output_add ctx 3 (96 - (s + 3))
  have hstate := Wychelean.Hashes.SHA3.SHAKE128.squeeze_state_add ctx 3 (96 - (s + 3))
  rw [show 3 + (96 - (s + 3)) = 96 - s by omega] at hsplit hstate
  simp only [XOF.Squeeze] at hL ⊢
  rw [← hsplit] at hL
  refine ⟨?_, ?_, hstate⟩
  · intro t ht hd
    have h1 := congrArg (fun l => l[t]?) hL
    simp only [List.getElem?_map, List.getElem?_drop] at h1
    rw [List.getElem?_append_left (by simp; omega)] at h1
    rw [List.getElem?_eq_getElem hd, List.getElem?_eq_getElem (by simp; omega)] at h1
    simpa using h1
  · have h2 := congrArg (List.drop 3) hL
    rw [← List.map_drop, List.drop_drop, List.drop_append_of_le_length (by simp)] at h2
    rw [h2]
    simp


/-! ### `sample_ntt`: the Rust loop -/

theorem nttStep_tt (C : ByteVec 3) (j : ℕ) (a : Vector Zq 256)
    (h1 : C[0].toNat + 256 * (C[1].toNat % 16) < q) (hj : j < 256)
    (h2 : C[1].toNat / 16 + 16 * C[2].toNat < q) (hj1 : j + 1 < 256) :
    nttStep C j a = (j + 1 + 1, (a.set j ((C[0].toNat + 256 * (C[1].toNat % 16) : ℕ) : Zq) hj).set (j + 1)
      ((C[1].toNat / 16 + 16 * C[2].toNat : ℕ) : Zq) hj1) := by
  simp [nttStep, h1, hj, h2, hj1]

theorem nttStep_tf (C : ByteVec 3) (j : ℕ) (a : Vector Zq 256)
    (h1 : C[0].toNat + 256 * (C[1].toNat % 16) < q) (hj : j < 256)
    (h2 : ¬ (C[1].toNat / 16 + 16 * C[2].toNat < q ∧ j + 1 < 256)) :
    nttStep C j a = (j + 1, a.set j ((C[0].toNat + 256 * (C[1].toNat % 16) : ℕ) : Zq) hj) := by
  simp only [nttStep, h1, hj, and_self, _root_.dite_true]
  exact dif_neg h2

theorem nttStep_ft (C : ByteVec 3) (j : ℕ) (a : Vector Zq 256)
    (h1 : ¬ C[0].toNat + 256 * (C[1].toNat % 16) < q) (hj : j < 256)
    (h2 : C[1].toNat / 16 + 16 * C[2].toNat < q) :
    nttStep C j a = (j + 1, a.set j ((C[1].toNat / 16 + 16 * C[2].toNat : ℕ) : Zq) hj) := by
  simp [nttStep, h1, hj, h2]

theorem nttStep_ff (C : ByteVec 3) (j : ℕ) (a : Vector Zq 256)
    (h1 : ¬ C[0].toNat + 256 * (C[1].toNat % 16) < q)
    (h2 : ¬ C[1].toNat / 16 + 16 * C[2].toNat < q) :
    nttStep C j a = (j, a) := by
  simp [nttStep, h1, h2]

/-- The Rust reader `B` and buffer `data[start..]` are what remains of squeezing 96 - start bytes
from the spec's XOF state `ctx`. -/
def NttInv (ctx : XofState) (B : shake.ShakeReader_168) (data : Std.Array U8 96#usize) (start : ℕ) : Prop :=
  start ≤ 96 ∧ start % 3 = 0 ∧ B = (XOF.Squeeze ctx (96 - start)).1 ∧
  (data.val.drop start).map toByte = (XOF.Squeeze ctx (96 - start)).2.toList

theorem toByte_toNat (x : U8) : (toByte x).toNat = x.val := rfl

theorem u16_size_eq : U16.size = 65536 := by simp [U16.size, U16.numBits]

theorem shl_u16 (x n : ℕ) (h : x * 2^n < 65536) : x <<< n % U16.size = x * 2^n := by
  rw [u16_size_eq, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt h

@[local step] theorem fromU16U8_spec (x : U8) :
    lift (core.convert.num.FromU16U8.from x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact core.convert.num.FromU16U8.from_val_eq x

theorem toVector_set (m : ℕ) (out : Coeffs) (j : Usize) (hj : j.val < 256) (x : U16) :
    Coeffs.toVector m (out.set j x) = (Coeffs.toVector m out).set j.val (toZMod m x) hj := by
  apply Vector.ext
  intro k hk
  simp only [Coeffs.toVector, Vector.getElem_ofFn, Std.Array.set_val_eq, Vector.getElem_set]
  by_cases h : j.val = k
  · subst h; simp
  · simp [h, List.getElem_set_ne h]

theorem bounded_set (m : ℕ) (out : Coeffs) (j : Usize) (x : U16) (hb : out.Bounded m)
    (hx : x.val < m) : Coeffs.Bounded m (out.set j x) := by
  intro y hy
  rw [Std.Array.set_val_eq] at hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hb y h
  · rw [h]; exact hx

theorem set_incr_spec (out : Coeffs) (j : Usize) (x : U16) (hj : j.val < 256) :
    (do
      let (_, back) ← Std.Array.index_mut_usize out j
      let j2 ← j + 1#usize
      ok (back x, j2)) ⦃ out' j' => out' = out.set j x ∧ j'.val = j.val + 1 ⦄ := by
  step*
  exact ⟨by rw [back_post], j2_post⟩

theorem ok_pair_spec {α β : Type} (a : α) (b : β) : (ok (a, b) : Result (α × β)) ⦃ x y => x = a ∧ y = b ⦄ := by
  simp [WP.spec_ok]

theorem usize_lt_iff (a b : Usize) : a < b ↔ a.val < b.val := Iff.rfl

theorem usize_lt_of_val (a b : Usize) (h : a.val < b.val) : a < b := h

theorem read168_spec (B : shake.ShakeReader_168) (s : Slice U8) :
    shake.ShakeReader_168_XofReader.read_168168 B s ⦃ B2 s2 =>
      B2 = (XOF.Squeeze B s.length).1 ∧
      s2.val = (XOF.Squeeze B s.length).2.toList.map (fun x => (⟨x.toBitVec⟩ : U8)) ⦄ := by
  simp only [shake.ShakeReader_168_XofReader.read_168168, Model.shake128Read, WP.spec_ok]
  refine ⟨rfl, ?_⟩
  rw [Slice.from_val]
  rfl

theorem refill_spec (ctx : XofState) (B : shake.ShakeReader_168) (data : Std.Array U8 96#usize)
    (start i : Usize) (hi : i.val = 96) (hinv : NttInv ctx B data start.val) :
    (if start = i then
        do
        let (s1, to_slice_mut_back) ← lift (Std.Array.to_slice_mut data)
        let (B2, s2) ← shake.ShakeReader_168_XofReader.read_168168 B s1
        ok (B2, to_slice_mut_back s2, 0#usize)
      else ok (B, data, start)) ⦃ B1 data1 start1 =>
        NttInv ctx B1 data1 start1.val ∧ start1.val + 3 ≤ 96 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have := read168_spec
  split
  · rename_i hs
    have hs' : start.val = 96 := by rw [hs, hi]
    rw [hs', Nat.sub_self, squeeze_zero_state] at h3
    subst h3
    step*
    have hl : s1.length = 96 := by
      have : s1.val.length = 96 := by rw [s1_post]; exact data.property
      exact this
    rw [hl] at B2_post B2_post1
    have h0 : ((0#usize : Usize).val) = 0 := rfl
    rw [h0]
    refine ⟨⟨by simp, by simp, B2_post, ?_⟩, by simp⟩
    rw [to_slice_mut_back_post, Std.Array.from_slice_val _ _ (by rw [B2_post1]; simp)]
    simp only [Nat.sub_zero, List.drop_zero, B2_post1, List.map_map]
    conv => rhs; rw [← List.map_id (Vector.toList _)]
    apply List.map_congr_left
    intro x _
    simp [toByte]
  · rename_i hs
    simp only [WP.spec_ok]
    have : start.val ≠ 96 := fun h => hs (by scalar_tac)
    exact ⟨⟨h1, h2, h3, h4⟩, by omega⟩

set_option maxHeartbeats 4000000 in
theorem sample_ntt_loop_spec (n : ℕ) : ∀ (ctx : XofState) (a : Vector Zq 256)
    (s' : MProd XofState (MProd ℕ (Vector Zq 256)))
    (B : shake.ShakeReader_168) (out : Coeffs) (data : Std.Array U8 96#usize) (start j : Usize),
    runN nttF n ⟨ctx, j.val, a⟩ = some s' →
    NttInv ctx B data start.val → j.val ≤ 256 → out.Bounded q → out.toVector q = a →
    algebra.sample_ntt_ShakeReader_168ShakeReader_168_loop B out data start j
      ⦃ (r : Coeffs) (_ : shake.ShakeReader_168) => r.Bounded q ∧ r.toVector q = s'.2.2 ⦄ := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [runN] at h
  | succ n ih =>
    intro ctx a s' B out data start j hrun hinv hj hb hout
    unfold algebra.sample_ntt_ShakeReader_168ShakeReader_168_loop
    simp only [runN, nttF] at hrun
    split
    · rename_i hj256
      have hj' : j.val < 256 := by scalar_tac
      simp only [hj', if_true] at hrun
      simp only [core.slice.SliceU8.lenU8]
      step as ⟨sl, hsl⟩
      step with refill_spec ctx B data start sl.len (by rw [hsl]; simp) hinv as ⟨B1, data1, start1, hinv1, hst1⟩
      obtain ⟨hbytes, hdrop, hstate⟩ := inv_step ctx data1.val start1.val hst1 hinv1.2.2.2
      simp only [aeneas_mono.array_index_u8_96,
        hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
        module_lattice.algebra.Elem_BaseField.new_BaseFieldBaseField]
      have hl1 : data1.val.length = 96 := by simp
      have hd0 := hbytes 0 (by omega) (by omega)
      have hd1 := hbytes 1 (by omega) (by omega)
      have hd2 := hbytes 2 (by omega) (by omega)
      step*
      · have := i13.hBounds
        have : i9.val < 256 := by rw [i9_post, i8_post]; exact (data1.val[i3.val]'(by scalar_tac)).hBounds
        have : i13.val < 256 := by rw [i13_post, i12_post]; exact (data1.val[i11.val]'(by scalar_tac)).hBounds
        rw [i10_post, i14_post, Nat.shiftRight_eq_div_pow, shl_u16 _ _ (by omega)]
        scalar_tac
      have hb1 : i1.val < 256 := i1.hBounds
      have hb4 : i4.val < 256 := i4.hBounds
      have hb12 : i12.val < 256 := i12.hBounds
      simp only [add_zero] at hd0
      have hC0 : ((XOF.Squeeze ctx 3).2[0]).toNat = i1.val := by rw [← hd0, toByte_toNat, i1_post]
      have hC1 : ((XOF.Squeeze ctx 3).2[1]).toNat = i4.val := by
        rw [← hd1, toByte_toNat, i4_post]; simp only [i3_post]
      have hC2 : ((XOF.Squeeze ctx 3).2[2]).toNat = i12.val := by
        rw [← hd2, toByte_toNat, i12_post]; simp only [i11_post]
      have hv1 : d1.val = ((XOF.Squeeze ctx 3).2[0]).toNat + 256 * (((XOF.Squeeze ctx 3).2[1]).toNat % 16) := by
        have h6 : i6.val = i4.val % 16 := by
          rw [i6_post, UScalar.val_and, i5_post, show (15#u16).val = 2^4 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]
        rw [hC0, hC1, d1_post, i2_post, i7_post, shl_u16 _ _ (by rw [h6]; omega), h6]
        ring
      have hv2 : d2.val = ((XOF.Squeeze ctx 3).2[1]).toNat / 16 + 16 * ((XOF.Squeeze ctx 3).2[2]).toNat := by
        have h9 : i9.val = i4.val := by rw [i9_post, i8_post, i4_post]
        rw [hC1, hC2, d2_post, i10_post, i14_post, Nat.shiftRight_eq_div_pow,
          shl_u16 _ _ (by rw [i13_post]; omega), h9, i13_post]
        ring
      have hinv' : NttInv (XOF.Squeeze ctx 3).1 B1 data1 start2.val := by
        obtain ⟨a1, a2, a3, a4⟩ := hinv1
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rw [start2_post, a3, hstate]
        · rw [start2_post]; exact hdrop
      generalize (XOF.Squeeze ctx 3).2 = C at hv1 hv2 hrun
      clear hC0 hC1 hC2 hd0 hd1 hd2 hbytes hdrop hstate hinv1
      have e1 : (d1.val < 3329) ↔ (C[0].toNat + 256 * (C[1].toNat % 16) < q) := by rw [hv1]
      have e2 : (d2.val < 3329) ↔ (C[1].toNat / 16 + 16 * C[2].toNat < q) := by rw [hv2]
      have hv1' : toZMod q d1 = ((C[0].toNat + 256 * (C[1].toNat % 16) : ℕ) : Zq) := by
        unfold toZMod; rw [hv1]
      have hv2' : toZMod q d2 = ((C[1].toNat / 16 + 16 * C[2].toNat : ℕ) : Zq) := by
        unfold toZMod; rw [hv2]
      have hQ : ∀ x : U16, (x < algebra.BaseField_Field.Q) ↔ x.val < 3329 := by
        intro x; rw [← Q_val]; rfl
      by_cases h1 : d1.val < 3329
      · rw [if_pos ((hQ d1).mpr h1)]
        have hl1 : j.val < out.length := by
          rw [Std.Array.length, Std.Array.length_eq]; have : (256#usize : Usize).val = 256 := rfl; omega
        step with Std.Array.index_mut_usize_spec out j hl1 as ⟨x, hx1, hx2⟩
        obtain ⟨y, back⟩ := x
        step with Usize.add_spec as ⟨j2, hj2⟩
        have eback : back = out.set j := by simpa using hx2
        subst eback
        have h1' := e1.mp h1
        have hb1 := bounded_set q out j d1 hb h1
        by_cases h2 : d2.val < 3329 ∧ j2.val < 256
        · rw [if_pos ((hQ d2).mpr h2.1), if_pos (usize_lt_of_val j2 256#usize (by simp; omega))]
          have hl2 : j2.val < (out.set j d1).length := by
            rw [Std.Array.length, Std.Array.length_eq]; exact h2.2
          step with Std.Array.index_mut_usize_spec (out.set j d1) j2 hl2 as ⟨y', back', hy', hback'⟩
          step with Usize.add_spec as ⟨j3, hj3⟩
          subst hback'
          have h2' := e2.mp h2.1
          rw [nttStep_tt C j.val a h1' hj' h2' (by omega)] at hrun
          apply ih (XOF.Squeeze ctx 3).1 _ s' B1 _ data1 start2 j3 _ hinv' (by omega)
            (bounded_set _ _ _ _ hb1 h2.1) rfl
          rw [toVector_set _ _ _ (by omega), toVector_set _ _ _ (by omega), hout, hv1', hv2']
          simp only [hj3, hj2]
          exact hrun
        · rw [nttStep_tf C j.val a h1' hj' (by intro hc; apply h2; exact ⟨e2.mpr hc.1, by omega⟩)] at hrun
          have hcont : algebra.sample_ntt_ShakeReader_168ShakeReader_168_loop B1 (out.set j d1) data1 start2 j2
              ⦃ r _ => Coeffs.Bounded q r ∧ Coeffs.toVector q r = s'.snd.snd ⦄ := by
            apply ih (XOF.Squeeze ctx 3).1 _ s' B1 _ data1 start2 j2 _ hinv' (by omega) hb1 rfl
            rw [toVector_set _ _ _ (by omega), hout, hv1', hj2]
            exact hrun
          by_cases h2a : d2.val < 3329
          · have h2b : ¬ j2.val < 256 := fun h => h2 ⟨h2a, h⟩
            rw [if_pos ((hQ d2).mpr h2a), if_neg (fun h => h2b (by have := (usize_lt_iff j2 256#usize).mp h; simpa using this))]
            exact hcont
          · rw [if_neg (fun h => h2a ((hQ d2).mp h))]
            exact hcont
      · rw [if_neg (fun h => h1 ((hQ d1).mp h))]
        rw [Std.bind_ok, Std.uncurry_apply_pair]
        have hl1 : j.val < out.length := by
          rw [Std.Array.length, Std.Array.length_eq]; exact hj'
        by_cases h2 : d2.val < 3329
        · rw [nttStep_ft C j.val a (fun h => h1 (e1.mpr h)) hj' (e2.mp h2)] at hrun
          rw [if_pos ((hQ d2).mpr h2), if_pos (usize_lt_of_val j 256#usize hj')]
          step with Std.Array.index_mut_usize_spec out j hl1 as ⟨y, back, hy, hback⟩
          step with Usize.add_spec as ⟨j2, hj2⟩
          subst hback
          apply ih (XOF.Squeeze ctx 3).1 _ s' B1 _ data1 start2 j2 _ hinv' (by omega)
            (bounded_set _ _ _ _ hb h2) rfl
          rw [toVector_set _ _ _ hj', hout, hv2']
          simp only [hj2]
          exact hrun
        · rw [nttStep_ff C j.val a (fun h => h1 (e1.mpr h)) (fun h => h2 (e2.mpr h))] at hrun
          rw [if_neg (fun h => h2 ((hQ d2).mp h))]
          exact ih (XOF.Squeeze ctx 3).1 a s' B1 out data1 start2 j hrun hinv' hj hb hout
    · rename_i hj256
      have hj' : ¬ j.val < 256 := by scalar_tac
      simp only [hj', if_false] at hrun
      simp only [Option.some.injEq] at hrun
      subst hrun
      simp only [WP.spec_ok]
      exact ⟨hb, hout⟩

theorem sample_ntt_spec (ctx : XofState) (n : ℕ) (s' : MProd XofState (MProd ℕ (Vector Zq 256)))
    (hrun : runN nttF n ⟨ctx, 0, Vector.replicate 256 0⟩ = some s') :
    algebra.sample_ntt_ShakeReader_168ShakeReader_168 ctx
      ⦃ (r : Coeffs) (_ : shake.ShakeReader_168) => r.Bounded q ∧ r.toVector q = s'.2.2 ⦄ := by
  unfold algebra.sample_ntt_ShakeReader_168ShakeReader_168
  simp only [hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    module_lattice.algebra.NttPolynomial_BaseField.new_BaseFieldBaseField, Std.bind_ok]
  step with Std.Array.to_slice_mut_spec as ⟨s1, back, hs1, hback⟩
  step with read168_spec as ⟨B1, s2, hB1, hs2⟩
  have hl : s1.length = 96 := by
    have : s1.val.length = 96 := by rw [hs1]; simp
    exact this
  rw [hl] at hB1 hs2
  have hinv : NttInv ctx B1 (back s2) (0#usize).val := by
    have h0 : ((0#usize : Usize).val) = 0 := rfl
    rw [h0]
    refine ⟨by simp, by simp, hB1, ?_⟩
    rw [hback, Std.Array.from_slice_val _ _ (by rw [hs2]; simp)]
    simp only [Nat.sub_zero, List.drop_zero, hs2, List.map_map]
    conv => rhs; rw [← List.map_id (Vector.toList _)]
    apply List.map_congr_left
    intro x _
    simp [toByte]
  apply sample_ntt_loop_spec n ctx _ s' B1 _ (back s2) 0#usize 0#usize hrun hinv (by simp)
  · intro x hx
    rw [Std.Array.repeat_val] at hx
    rw [List.eq_of_mem_replicate hx]; simp
  · apply Vector.ext
    intro k hk
    simp only [Coeffs.toVector, Vector.getElem_ofFn, Std.Array.repeat_val, List.getElem_replicate,
      toZMod, Vector.getElem_replicate]
    simp

/-! ### `matrix_sample_ntt` -/

/-- Rejection sampling (Algorithm 7) on the XOF stream of `B` accepts 256 coefficients after
finitely many 3-byte blocks. This is a property of SHAKE128's output that we cannot prove; the
Rust loop diverges exactly when it fails. -/
def SampleNTTTerminates (B : ByteVec (seedLen + 2)) : Prop :=
  ∃ n s', runN nttF n ⟨XOF.Finalize (XOF.Absorb XOF.Init B), 0, Vector.replicate 256 0⟩ = some s'

theorem sample_ntt_spec' (B : ByteVec (seedLen + 2)) (h : SampleNTTTerminates B) :
    algebra.sample_ntt_ShakeReader_168ShakeReader_168 (XOF.Finalize (XOF.Absorb XOF.Init B))
      ⦃ (r : Coeffs) (_ : shake.ShakeReader_168) => r.Bounded q ∧ r.toTq = SampleNTT B ⦄ := by
  obtain ⟨n, s', hrun⟩ := h
  apply WP.spec_mono (sample_ntt_spec _ n s' hrun)
  rintro ⟨r, _⟩ ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rw [SampleNTT_eq B n s' hrun, Coeffs.toTq, h2]

/-- The entry `Â[r, c]` of the (possibly transposed) matrix. -/
def matEntry (ρ : ByteVec 32) (transpose : Bool) (r c : ℕ) : Tq :=
  if transpose then SampleNTT (ρ ++ #v[UInt8.ofNat r, UInt8.ofNat c])
  else SampleNTT (ρ ++ #v[UInt8.ofNat c, UInt8.ofNat r])

theorem truncate_u8_toByte (x : Usize) (h : x.val < 256) :
    module_lattice.truncate.u8_Truncate_usize.truncate x ⦃ r => toByte r = UInt8.ofNat x.val ⦄ := by
  apply WP.spec_mono (truncate_u8_spec x h)
  intro r hr
  exact toByte_eq_ofNat r _ hr

/-- All entries of the `k × k` matrix generated from `ρ` are sampled by terminating loops. -/
def AllTerminate (ρ : ByteVec 32) (k : ℕ) : Prop :=
  ∀ a b, a < k → b < k → SampleNTTTerminates (ρ ++ #v[UInt8.ofNat a, UInt8.ofNat b])

/-- Entry `(r, c)` of a Rust matrix. -/
def ent {K : Usize} (A : Std.Array (Std.Array Coeffs K) K) (r c : ℕ) : Coeffs :=
  if h : r < K.val ∧ c < K.val then
    (A.val[r]'(by have := A.property; omega)).val[c]'(by have := (A.val[r]'(by have := A.property; omega)).property; omega)
  else Std.Array.repeat 256#usize 0#u16

theorem ent_set {K : Usize} (A : Std.Array (Std.Array Coeffs K) K) (i j : Usize) (x : Coeffs)
    (hi : i.val < K.val) (_hj : j.val < K.val) (r c : ℕ) (hr : r < K.val) (hc : c < K.val) :
    ent (A.set i ((A.val[i.val]'(by have := A.property; omega)).set j x)) r c =
      if r = i.val ∧ c = j.val then x else ent A r c := by
  unfold ent
  simp only [dif_pos (show r < K.val ∧ c < K.val from ⟨hr, hc⟩), Std.Array.set_val_eq,
    List.getElem_set]
  by_cases h1 : i.val = r <;> by_cases h2 : j.val = c
  · subst h1 h2; simp
  · simp [h1, h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]
  · simp [h1, Ne.symm h1]

theorem mat2_inner_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat2) (i : Usize) (hi : i.val < 2) (hend : iter.end.val = 2) (hs : iter.start.val ≤ 2)
    (HT : AllTerminate (arrayToBytes ρ) 2) :
    algebra.matrix_sample_ntt_U2U2_loop0_loop0 iter ρ tr A i ⦃ A' => ∀ r c, r < 2 → c < 2 →
      if r = i.val ∧ iter.start.val ≤ c then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U2U2_loop0_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U2_U2_IndexMut_usize.index_mut_NttVector_BaseField_U2_usize_U2NttVector_BaseField_U2UsizeU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U2NttPolynomial_BaseFieldUsizeU2]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ c := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some j =>
    have hs' : iter.start.val < 2 := by split_ifs at ho <;> simp_all
    have hji : j = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hji
    simp only
    have hl0 : i.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hi
    cases tr
    · rw [if_neg (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte iter.start (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte i (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT iter.start.val i.val hs' hi
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat2_inner_spec iter1 ρ false _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
    · rw [if_pos (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte i (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte iter.start (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT i.val iter.start.val hi hs'
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat2_inner_spec iter1 ρ true _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
termination_by 2 - iter.start.val
decreasing_by all_goals omega

theorem mat2_outer_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat2) (hend : iter.end.val = 2) (hs : iter.start.val ≤ 2)
    (HT : AllTerminate (arrayToBytes ρ) 2) :
    algebra.matrix_sample_ntt_U2U2_loop0 iter ρ tr A ⦃ A' => ∀ r c, r < 2 → c < 2 →
      if iter.start.val ≤ r then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U2U2_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U2_U2_Index_usize.index_NttVector_BaseField_U2_usize_U2NttVector_BaseField_U2UsizeU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Deref.deref_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ r := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some i =>
    have hs' : iter.start.val < 2 := by split_ifs at ho <;> simp_all
    have hii : i = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hii
    simp only
    have hl0 : iter.start.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hs'
    apply WP.spec_bind (Std.Array.index_usize_spec A iter.start hl0)
    intro row hrow
    apply WP.spec_bind (mat2_inner_spec _ ρ tr A iter.start hs' (by simp [Slice.len, Std.Array.to_slice])
      (by simp) HT)
    intro A1 hA1
    apply WP.spec_mono (mat2_outer_spec iter1 ρ tr A1 (by rw [hend1, hend]) (by omega) HT)
    intro A' hA' r c hr hc
    have h := hA' r c hr hc
    have h1 := hA1 r c hr hc
    have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice row).len } : core.ops.range.Range Usize).start).val = 0 := rfl
    rw [h0] at h1
    simp only [Nat.zero_le, and_true] at h1
    by_cases hc1 : iter.start.val ≤ r
    · rw [if_pos hc1]
      by_cases hc2 : r = iter.start.val
      · have : ¬ iter1.start.val ≤ r := by omega
        rw [if_neg this] at h
        rw [if_pos hc2] at h1
        rw [h]; exact h1
      · have : iter1.start.val ≤ r := by omega
        rw [if_pos this] at h
        exact h
    · rw [if_neg hc1]
      have : ¬ iter1.start.val ≤ r := by omega
      rw [if_neg this] at h
      rw [if_neg (by omega)] at h1
      rw [h, h1]
termination_by 2 - iter.start.val
decreasing_by all_goals omega

theorem ent_eq {K : Usize} (A : Std.Array (Std.Array Coeffs K) K) (r c : ℕ) (hr : r < K.val)
    (hc : c < K.val) (h1 : r < A.val.length) (h2 : c < (A.val[r]'h1).val.length) :
    (A.val[r]'h1).val[c]'h2 = ent A r c := by
  simp [ent, hr, hc]

theorem mat_post {K : Usize} (ρ : Std.Array U8 32#usize) (tr : Bool) (A : Std.Array (Std.Array Coeffs K) K)
    (hA : ∀ r c, r < K.val → c < K.val →
      Coeffs.Bounded q (ent A r c) ∧ (ent A r c).toTq = matEntry (arrayToBytes ρ) tr r c) :
    Mat.Bounded q A ∧ toNTTMat A = if tr then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix K.val (arrayToBytes ρ))
      else sampleMatrix K.val (arrayToBytes ρ) := by
  have hlen : A.val.length = K.val := A.property
  have hrow : ∀ k (hk : k < A.val.length), (A.val[k]'hk).val.length = K.val := fun k hk => (A.val[k]'hk).property
  refine ⟨?_, ?_⟩
  · intro row hrowm a ha
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hrowm
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem ha
    rw [ent_eq A r c (by omega) (by rw [hrow] at hc; omega)]
    exact (hA r c (by omega) (by rw [hrow] at hc; omega)).1
  · apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    simp only [toNTTMat, toNTTVec, Vector.getElem_ofFn]
    rw [ent_eq A r c hr hc, (hA r c hr hc).2]
    cases tr
    · simp [matEntry, sampleMatrix]
    · simp [matEntry, sampleMatrix, Wychelean.Utils.Linear.Mat.transpose]

theorem matrix_sample_ntt_spec_2_of (ρ : Std.Array U8 32#usize) (tr : Bool)
    (HT : AllTerminate (arrayToBytes ρ) 2) :
    algebra.matrix_sample_ntt_U2U2 ρ tr
      ⦃ (A : Mat2) => Mat.Bounded q A ∧ toNTTMat A = if tr then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 2 (arrayToBytes ρ)) else sampleMatrix 2 (arrayToBytes ρ) ⦄ := by
  unfold algebra.matrix_sample_ntt_U2U2
  simp only [module_lattice.algebra.NttMatrix_BaseField_U2_U2_Default.default_BaseField_U2_U2BaseFieldU2U2,
    hybrid_array.Array_NttVector_BaseField_U2_U2_Default.default_NttVector_BaseField_U2_U2NttVector_BaseField_U2U2,
    hybrid_array.Array_NttVector_BaseField_U2_U2_Deref.deref_NttVector_BaseField_U2_U2NttVector_BaseField_U2U2,
    core.slice.SliceNttVector_BaseField_U2.lenNttVector_BaseField_U2,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, Std.bind_ok]
  apply WP.spec_bind (mat2_outer_spec _ ρ tr _ (by simp [Slice.len, Std.Array.to_slice]) (by simp) HT)
  intro A hA
  simp only [WP.spec_ok]
  apply mat_post ρ tr A
  intro r c hr hc
  have h := hA r c hr hc
  have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice (Std.Array.repeat 2#usize
    (Std.Array.repeat 2#usize (Std.Array.repeat 256#usize 0#u16)))).len } : core.ops.range.Range Usize).start).val = 0 := rfl
  rw [h0, if_pos (Nat.zero_le _)] at h
  exact h

theorem mat3_inner_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat3) (i : Usize) (hi : i.val < 3) (hend : iter.end.val = 3) (hs : iter.start.val ≤ 3)
    (HT : AllTerminate (arrayToBytes ρ) 3) :
    algebra.matrix_sample_ntt_U3U3_loop0_loop0 iter ρ tr A i ⦃ A' => ∀ r c, r < 3 → c < 3 →
      if r = i.val ∧ iter.start.val ≤ c then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U3U3_loop0_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U3_U3_IndexMut_usize.index_mut_NttVector_BaseField_U3_usize_U3NttVector_BaseField_U3UsizeU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U3NttPolynomial_BaseFieldUsizeU3]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ c := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some j =>
    have hs' : iter.start.val < 3 := by split_ifs at ho <;> simp_all
    have hji : j = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hji
    simp only
    have hl0 : i.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hi
    cases tr
    · rw [if_neg (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte iter.start (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte i (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT iter.start.val i.val hs' hi
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat3_inner_spec iter1 ρ false _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
    · rw [if_pos (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte i (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte iter.start (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT i.val iter.start.val hi hs'
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat3_inner_spec iter1 ρ true _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
termination_by 3 - iter.start.val
decreasing_by all_goals omega

theorem mat3_outer_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat3) (hend : iter.end.val = 3) (hs : iter.start.val ≤ 3)
    (HT : AllTerminate (arrayToBytes ρ) 3) :
    algebra.matrix_sample_ntt_U3U3_loop0 iter ρ tr A ⦃ A' => ∀ r c, r < 3 → c < 3 →
      if iter.start.val ≤ r then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U3U3_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U3_U3_Index_usize.index_NttVector_BaseField_U3_usize_U3NttVector_BaseField_U3UsizeU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Deref.deref_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ r := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some i =>
    have hs' : iter.start.val < 3 := by split_ifs at ho <;> simp_all
    have hii : i = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hii
    simp only
    have hl0 : iter.start.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hs'
    apply WP.spec_bind (Std.Array.index_usize_spec A iter.start hl0)
    intro row hrow
    apply WP.spec_bind (mat3_inner_spec _ ρ tr A iter.start hs' (by simp [Slice.len, Std.Array.to_slice])
      (by simp) HT)
    intro A1 hA1
    apply WP.spec_mono (mat3_outer_spec iter1 ρ tr A1 (by rw [hend1, hend]) (by omega) HT)
    intro A' hA' r c hr hc
    have h := hA' r c hr hc
    have h1 := hA1 r c hr hc
    have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice row).len } : core.ops.range.Range Usize).start).val = 0 := rfl
    rw [h0] at h1
    simp only [Nat.zero_le, and_true] at h1
    by_cases hc1 : iter.start.val ≤ r
    · rw [if_pos hc1]
      by_cases hc2 : r = iter.start.val
      · have : ¬ iter1.start.val ≤ r := by omega
        rw [if_neg this] at h
        rw [if_pos hc2] at h1
        rw [h]; exact h1
      · have : iter1.start.val ≤ r := by omega
        rw [if_pos this] at h
        exact h
    · rw [if_neg hc1]
      have : ¬ iter1.start.val ≤ r := by omega
      rw [if_neg this] at h
      rw [if_neg (by omega)] at h1
      rw [h, h1]
termination_by 3 - iter.start.val
decreasing_by all_goals omega

theorem matrix_sample_ntt_spec_3_of (ρ : Std.Array U8 32#usize) (tr : Bool)
    (HT : AllTerminate (arrayToBytes ρ) 3) :
    algebra.matrix_sample_ntt_U3U3 ρ tr
      ⦃ (A : Mat3) => Mat.Bounded q A ∧ toNTTMat A = if tr then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 3 (arrayToBytes ρ)) else sampleMatrix 3 (arrayToBytes ρ) ⦄ := by
  unfold algebra.matrix_sample_ntt_U3U3
  simp only [module_lattice.algebra.NttMatrix_BaseField_U3_U3_Default.default_BaseField_U3_U3BaseFieldU3U3,
    hybrid_array.Array_NttVector_BaseField_U3_U3_Default.default_NttVector_BaseField_U3_U3NttVector_BaseField_U3U3,
    hybrid_array.Array_NttVector_BaseField_U3_U3_Deref.deref_NttVector_BaseField_U3_U3NttVector_BaseField_U3U3,
    core.slice.SliceNttVector_BaseField_U3.lenNttVector_BaseField_U3,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, Std.bind_ok]
  apply WP.spec_bind (mat3_outer_spec _ ρ tr _ (by simp [Slice.len, Std.Array.to_slice]) (by simp) HT)
  intro A hA
  simp only [WP.spec_ok]
  apply mat_post ρ tr A
  intro r c hr hc
  have h := hA r c hr hc
  have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice (Std.Array.repeat 3#usize
    (Std.Array.repeat 3#usize (Std.Array.repeat 256#usize 0#u16)))).len } : core.ops.range.Range Usize).start).val = 0 := rfl
  rw [h0, if_pos (Nat.zero_le _)] at h
  exact h

theorem mat4_inner_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat4) (i : Usize) (hi : i.val < 4) (hend : iter.end.val = 4) (hs : iter.start.val ≤ 4)
    (HT : AllTerminate (arrayToBytes ρ) 4) :
    algebra.matrix_sample_ntt_U4U4_loop0_loop0 iter ρ tr A i ⦃ A' => ∀ r c, r < 4 → c < 4 →
      if r = i.val ∧ iter.start.val ≤ c then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U4U4_loop0_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U4_U4_IndexMut_usize.index_mut_NttVector_BaseField_U4_usize_U4NttVector_BaseField_U4UsizeU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U4NttPolynomial_BaseFieldUsizeU4]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ c := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some j =>
    have hs' : iter.start.val < 4 := by split_ifs at ho <;> simp_all
    have hji : j = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hji
    simp only
    have hl0 : i.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hi
    cases tr
    · rw [if_neg (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte iter.start (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte i (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT iter.start.val i.val hs' hi
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat4_inner_spec iter1 ρ false _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
    · rw [if_pos (by simp), Std.bind_ok, Std.uncurry_apply_pair]
      step with truncate_u8_toByte i (by omega) as ⟨i2, hi2⟩
      step with truncate_u8_toByte iter.start (by omega) as ⟨i3, hi3⟩
      step with XOF_spec as ⟨xof, hxof⟩
      subst hxof
      have HT' := HT i.val iter.start.val hi hs'
      rw [← hi2, ← hi3] at HT'
      apply WP.spec_bind (sample_ntt_spec' _ HT')
      rintro ⟨npbf, B'⟩ ⟨hb, htq⟩
      try rw [Std.uncurry_apply_pair]
      apply WP.spec_bind (Std.Array.index_mut_usize_spec A i hl0)
      rintro ⟨row, back1⟩ ⟨hrow, hback1⟩
      try rw [Std.uncurry_apply_pair]
      have hl1 : iter.start.val < row.length := by
        rw [Std.Array.length, Std.Array.length_eq]; exact hs'
      apply WP.spec_bind (Std.Array.index_mut_usize_spec row iter.start hl1)
      rintro ⟨y, back2⟩ ⟨hy, hback2⟩
      try rw [Std.uncurry_apply_pair]
      subst hback1 hback2 hrow
      apply WP.spec_mono (mat4_inner_spec iter1 ρ true _ i hi (by rw [hend1, hend]) (by omega) HT)
      intro A' hA' r c hr hc
      have h := hA' r c hr hc
      rw [ent_set A i iter.start npbf hi hs' r c hr hc] at h
      by_cases hc1 : r = i.val ∧ iter.start.val ≤ c
      · rw [if_pos hc1]
        by_cases hc2 : c = iter.start.val
        · have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
          rw [if_neg this, if_pos ⟨hc1.1, hc2⟩] at h
          rw [h]
          refine ⟨hb, ?_⟩
          rw [htq, hi2, hi3, hc1.1, hc2]
          rfl
        · have : r = i.val ∧ iter1.start.val ≤ c := ⟨hc1.1, by omega⟩
          rw [if_pos this] at h
          exact h
      · rw [if_neg hc1]
        have : ¬ (r = i.val ∧ iter1.start.val ≤ c) := by omega
        rw [if_neg this, if_neg (by omega)] at h
        exact h
termination_by 4 - iter.start.val
decreasing_by all_goals omega

theorem mat4_outer_spec (iter : core.ops.range.Range Usize) (ρ : Std.Array U8 32#usize) (tr : Bool)
    (A : Mat4) (hend : iter.end.val = 4) (hs : iter.start.val ≤ 4)
    (HT : AllTerminate (arrayToBytes ρ) 4) :
    algebra.matrix_sample_ntt_U4U4_loop0 iter ρ tr A ⦃ A' => ∀ r c, r < 4 → c < 4 →
      if iter.start.val ≤ r then
        Coeffs.Bounded q (ent A' r c) ∧ (ent A' r c).toTq = matEntry (arrayToBytes ρ) tr r c
      else ent A' r c = ent A r c ⦄ := by
  unfold algebra.matrix_sample_ntt_U4U4_loop0
  simp only [hybrid_array.Array_NttVector_BaseField_U4_U4_Index_usize.index_NttVector_BaseField_U4_usize_U4NttVector_BaseField_U4UsizeU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Deref.deref_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step with range_next_spec as ⟨o, iter1, ho, hend1⟩
  cases o with
  | none =>
    simp only [WP.spec_ok]
    intro r c hr hc
    have : ¬ iter.start.val ≤ r := by split_ifs at ho <;> (simp_all; try omega)
    simp [this]
  | some i =>
    have hs' : iter.start.val < 4 := by split_ifs at ho <;> simp_all
    have hii : i = iter.start := by split_ifs at ho <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at ho <;> simp_all
    subst hii
    simp only
    have hl0 : iter.start.val < A.length := by rw [Std.Array.length, Std.Array.length_eq]; exact hs'
    apply WP.spec_bind (Std.Array.index_usize_spec A iter.start hl0)
    intro row hrow
    apply WP.spec_bind (mat4_inner_spec _ ρ tr A iter.start hs' (by simp [Slice.len, Std.Array.to_slice])
      (by simp) HT)
    intro A1 hA1
    apply WP.spec_mono (mat4_outer_spec iter1 ρ tr A1 (by rw [hend1, hend]) (by omega) HT)
    intro A' hA' r c hr hc
    have h := hA' r c hr hc
    have h1 := hA1 r c hr hc
    have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice row).len } : core.ops.range.Range Usize).start).val = 0 := rfl
    rw [h0] at h1
    simp only [Nat.zero_le, and_true] at h1
    by_cases hc1 : iter.start.val ≤ r
    · rw [if_pos hc1]
      by_cases hc2 : r = iter.start.val
      · have : ¬ iter1.start.val ≤ r := by omega
        rw [if_neg this] at h
        rw [if_pos hc2] at h1
        rw [h]; exact h1
      · have : iter1.start.val ≤ r := by omega
        rw [if_pos this] at h
        exact h
    · rw [if_neg hc1]
      have : ¬ iter1.start.val ≤ r := by omega
      rw [if_neg this] at h
      rw [if_neg (by omega)] at h1
      rw [h, h1]
termination_by 4 - iter.start.val
decreasing_by all_goals omega

theorem matrix_sample_ntt_spec_4_of (ρ : Std.Array U8 32#usize) (tr : Bool)
    (HT : AllTerminate (arrayToBytes ρ) 4) :
    algebra.matrix_sample_ntt_U4U4 ρ tr
      ⦃ (A : Mat4) => Mat.Bounded q A ∧ toNTTMat A = if tr then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 4 (arrayToBytes ρ)) else sampleMatrix 4 (arrayToBytes ρ) ⦄ := by
  unfold algebra.matrix_sample_ntt_U4U4
  simp only [module_lattice.algebra.NttMatrix_BaseField_U4_U4_Default.default_BaseField_U4_U4BaseFieldU4U4,
    hybrid_array.Array_NttVector_BaseField_U4_U4_Default.default_NttVector_BaseField_U4_U4NttVector_BaseField_U4U4,
    hybrid_array.Array_NttVector_BaseField_U4_U4_Deref.deref_NttVector_BaseField_U4_U4NttVector_BaseField_U4U4,
    core.slice.SliceNttVector_BaseField_U4.lenNttVector_BaseField_U4,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter, Std.bind_ok]
  apply WP.spec_bind (mat4_outer_spec _ ρ tr _ (by simp [Slice.len, Std.Array.to_slice]) (by simp) HT)
  intro A hA
  simp only [WP.spec_ok]
  apply mat_post ρ tr A
  intro r c hr hc
  have h := hA r c hr hc
  have h0 : (({ start := 0#usize, «end» := (Std.Array.to_slice (Std.Array.repeat 4#usize
    (Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u16)))).len } : core.ops.range.Range Usize).start).val = 0 := rfl
  rw [h0, if_pos (Nat.zero_le _)] at h
  exact h

end Sample

open Sample

/-- Rejection sampling (`SampleNTT`, Algorithm 7) halts on every input: SHAKE128's output always
contains 256 candidates `< q`. This is overwhelmingly likely, but no one can prove it for all
inputs, so the theorems whose Rust code samples a matrix assume it. (The Rust loop diverges where
the spec's `while` loop doesn't halt.) -/
def SampleNTTHalts : Prop := ∀ B : Wychelean.ByteVec (seedLen + 2), SampleNTTTerminates B

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_2 (hT : SampleNTTHalts) (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U2U2 ρ transpose
      ⦃ (A : Mat2) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 2 (arrayToBytes ρ)) else sampleMatrix 2 (arrayToBytes ρ) ⦄ := by
  exact Sample.matrix_sample_ntt_spec_2_of ρ transpose (fun _ _ _ _ => hT _)

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_3 (hT : SampleNTTHalts) (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U3U3 ρ transpose
      ⦃ (A : Mat3) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 3 (arrayToBytes ρ)) else sampleMatrix 3 (arrayToBytes ρ) ⦄ := by
  exact Sample.matrix_sample_ntt_spec_3_of ρ transpose (fun _ _ _ _ => hT _)

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_4 (hT : SampleNTTHalts) (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U4U4 ρ transpose
      ⦃ (A : Mat4) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 4 (arrayToBytes ρ)) else sampleMatrix 4 (arrayToBytes ρ) ⦄ := by
  exact Sample.matrix_sample_ntt_spec_4_of ρ transpose (fun _ _ _ _ => hT _)

-- INTERFACE
@[step] theorem sample_poly_cbd_spec_2 (B : Std.Array U8 128#usize) :
    algebra.sample_poly_cbd_U2U2 B
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = SamplePolyCBD (η := η₂) (arrayToBytes B) ⦄ := by
  unfold algebra.sample_poly_cbd_U2U2
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  have hb4 : ∀ k (hk : k < 256), (vals.val[k]'(by grind)).val < 16 := by
    intro k hk; exact vals_post _ (List.getElem_mem _)
  step with cbd2_loop_spec as ⟨r, hr⟩
  simp only [Nat.zero_le, if_true] at hr
  have hval : ∀ k (hk : k < 256), (vals.val[k]'(by grind)).val =
      (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k)).toNat * 1 + (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 1)).toNat * 2 +
      (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 2)).toNat * 4 + (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 3)).toNat * 8 := by
    intro k hk
    have h1 := congrArg (fun v => v[k]) vals_post1
    simp only [Coeffs.toVector, Vector.getElem_ofFn, toZMod] at h1
    rw [ByteDecode_coeff _ _ k hk] at h1
    simp only [Fin.sum_univ_four] at h1
    have e : ∀ j, @bitAt (32 * 4) (arrayToBytes B) j = @bitAt (64 * η₂) (arrayToBytes B) j := fun _ => rfl
    simp only [e] at h1
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at h2
    have hm : m 4 = 16 := rfl
    rw [hm] at h2
    have := hb4 k hk
    have b0 := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k))
    have b1 := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 1))
    have b2 := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 2))
    have b3 := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 3))
    rw [show k * 4 = 4 * k by ring] at h2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl,
      add_zero, pow_zero, pow_one] at h2
    norm_num at h2
    omega
  have hlen : r.val.length = 256 := r.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [hr k (by omega)]
    unfold onesVal
    exact Nat.mod_lt _ (by norm_num)
  · apply Polynomial.ext
    intro k hk
    rw [poly_getElem_eq_coeffs, poly_getElem_eq_coeffs, SamplePolyCBD_coeff_2 _ k hk]
    simp only [Coeffs.toPoly, Coeffs.toVector, Vector.getElem_ofFn]
    unfold toZMod
    rw [hr k hk, hval k hk]
    obtain ⟨h1, h2⟩ := cbd2_val (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k))
      (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 1)) (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 2))
      (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 3))
    unfold onesVal
    rw [h1, h2, cast_onesVal _ _ (by have := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 2)); have := Bool.toNat_le (bitAt (n := 64 * η₂) (arrayToBytes B) (4 * k + 3)); omega)]

-- INTERFACE
@[step] theorem sample_poly_cbd_spec_3 (B : Std.Array U8 192#usize) :
    algebra.sample_poly_cbd_U3U3 B
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = SamplePolyCBD (η := η₁ .ML_KEM_512) (arrayToBytes B) ⦄ := by
  unfold algebra.sample_poly_cbd_U3U3
  simp only [hybrid_array.Array_Elem_BaseField_U256_Deref.deref_Elem_BaseField_U256Elem_BaseFieldU256,
    core.slice.SliceElem_BaseField.lenElem_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  have hb4 : ∀ k (hk : k < 256), (vals.val[k]'(by grind)).val < 64 := by
    intro k hk; exact vals_post _ (List.getElem_mem _)
  step with cbd3_loop_spec as ⟨r, hr⟩
  simp only [Nat.zero_le, if_true] at hr
  have hval : ∀ k (hk : k < 256), (vals.val[k]'(by grind)).val =
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k)).toNat * 1 + (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 1)).toNat * 2 +
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 2)).toNat * 4 + (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 3)).toNat * 8 +
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 4)).toNat * 16 + (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 5)).toNat * 32 := by
    intro k hk
    have h1 := congrArg (fun v => v[k]) vals_post1
    simp only [Coeffs.toVector, Vector.getElem_ofFn, toZMod] at h1
    rw [ByteDecode_coeff _ _ k hk] at h1
    simp only [Fin.sum_univ_six] at h1
    have e : ∀ j, @bitAt (32 * 6) (arrayToBytes B) j = @bitAt (64 * η₁ .ML_KEM_512) (arrayToBytes B) j := fun _ => rfl
    simp only [e] at h1
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at h2
    have hm : m 6 = 64 := rfl
    rw [hm] at h2
    have := hb4 k hk
    have b0 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k))
    have b1 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 1))
    have b2 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 2))
    have b3 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 3))
    have b4 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 4))
    have b5 := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 5))
    rw [show k * 6 = 6 * k by ring] at h2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 6) : ℕ) = 3 from rfl,
      show ((4 : Fin 6) : ℕ) = 4 from rfl, show ((5 : Fin 6) : ℕ) = 5 from rfl,
      add_zero, pow_zero, pow_one] at h2
    norm_num at h2
    omega
  have hlen : r.val.length = 256 := r.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [hr k (by omega)]
    unfold onesVal
    exact Nat.mod_lt _ (by norm_num)
  · apply Polynomial.ext
    intro k hk
    rw [poly_getElem_eq_coeffs, poly_getElem_eq_coeffs, SamplePolyCBD_coeff_3 _ k hk]
    simp only [Coeffs.toPoly, Coeffs.toVector, Vector.getElem_ofFn]
    unfold toZMod
    rw [hr k hk, hval k hk]
    obtain ⟨h1, h2⟩ := cbd3_val (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k))
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 1)) (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 2))
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 3)) (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 4))
      (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 5))
    unfold onesVal
    rw [h1, h2, cast_onesVal _ _ (by
      have := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 3))
      have := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 4))
      have := Bool.toNat_le (bitAt (n := 64 * η₁ .ML_KEM_512) (arrayToBytes B) (6 * k + 5))
      omega)]


theorem Sample.vec_cbd_2_2_loop_spec (iter : core.ops.range.Range Usize) (σ : Std.Array U8 32#usize)
    (start_n : U8) (a : Vec2) (h : start_n.val + 2 < 256)
    (hend : iter.end.val = 2) (hstart : iter.start.val ≤ 2) :
    algebra.sample_poly_vec_cbd_U2_U2U2U2_loop iter σ start_n a ⦃ r => ∀ k (hk : k < 2),
      if iter.start.val ≤ k then
        Coeffs.Bounded q (r.val[k]'(by grind)) ∧
        Coeffs.toPoly q (r.val[k]'(by grind)) = SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + k)))
      else r.val[k]'(by grind) = a.val[k]'(by grind) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U2U2U2_loop
  simp only [hybrid_array.Array_Polynomial_BaseField_U2_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2]
  step*
  · intro k hk
    have : ¬ iter.start.val ≤ k := by split_ifs at o_post <;> (simp_all; try omega)
    simp [this]
  · have hs : iter.start.val < 2 := by split_ifs at o_post <;> simp_all
    have hi : i = iter.start := by split_ifs at o_post <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
    subst hi
    step with Sample.truncate_u8_spec as ⟨i_u8, hu8⟩
    step*
    have r_k := r_post k k_post
    rw [index_mut_Polynomial_BaseField_usize_U2_back_post] at r_k
    by_cases hk : k = iter.start.val
    · subst hk
      have : ¬ iter1.start.val ≤ iter.start.val := by omega
      simp only [this, if_false, le_refl, if_true] at r_k ⊢
      rw [r_k]
      simp only [Std.Array.set_val_eq]; simp_lists
      refine ⟨pbf_post, ?_⟩
      rw [pbf_post1, prf_output_post, Sample.toByte_eq_ofNat N _ (by rw [N_post, hu8])]
    · by_cases c : iter.start.val ≤ k
      · have c' : iter1.start.val ≤ k := by omega
        simp only [c, c', if_true] at r_k ⊢
        exact r_k
      · have c' : ¬ iter1.start.val ≤ k := by omega
        simp only [c, c', if_false] at r_k ⊢
        rw [r_k]
        simp only [Std.Array.set_val_eq]; simp_lists
termination_by 2 - iter.start.val
decreasing_by scalar_tac

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_2 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 2 < 256) :
    algebra.sample_poly_vec_cbd_U2_U2U2U2 σ start_n
      ⦃ (v : Vec2) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U2U2U2
  simp only [module_lattice.algebra.Vector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Default.default_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  step with Sample.vec_cbd_2_2_loop_spec as ⟨v, hv⟩
  simp only [Nat.zero_le, if_true] at hv
  have hlen : v.val.length = 2 := v.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hv k (by omega)).1
  · apply Vector.ext
    intro k hk
    simp only [toPolyVec, Vector.getElem_ofFn]
    exact (hv k hk).2

theorem Sample.vec_cbd_2_3_loop_spec (iter : core.ops.range.Range Usize) (σ : Std.Array U8 32#usize)
    (start_n : U8) (a : Vec3) (h : start_n.val + 3 < 256)
    (hend : iter.end.val = 3) (hstart : iter.start.val ≤ 3) :
    algebra.sample_poly_vec_cbd_U2_U3U2U3_loop iter σ start_n a ⦃ r => ∀ k (hk : k < 3),
      if iter.start.val ≤ k then
        Coeffs.Bounded q (r.val[k]'(by grind)) ∧
        Coeffs.toPoly q (r.val[k]'(by grind)) = SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + k)))
      else r.val[k]'(by grind) = a.val[k]'(by grind) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U3U2U3_loop
  simp only [hybrid_array.Array_Polynomial_BaseField_U3_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U3Polynomial_BaseFieldUsizeU3]
  step*
  · intro k hk
    have : ¬ iter.start.val ≤ k := by split_ifs at o_post <;> (simp_all; try omega)
    simp [this]
  · have hs : iter.start.val < 3 := by split_ifs at o_post <;> simp_all
    have hi : i = iter.start := by split_ifs at o_post <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
    subst hi
    step with Sample.truncate_u8_spec as ⟨i_u8, hu8⟩
    step*
    have r_k := r_post k k_post
    rw [index_mut_Polynomial_BaseField_usize_U3_back_post] at r_k
    by_cases hk : k = iter.start.val
    · subst hk
      have : ¬ iter1.start.val ≤ iter.start.val := by omega
      simp only [this, if_false, le_refl, if_true] at r_k ⊢
      rw [r_k]
      simp only [Std.Array.set_val_eq]; simp_lists
      refine ⟨pbf_post, ?_⟩
      rw [pbf_post1, prf_output_post, Sample.toByte_eq_ofNat N _ (by rw [N_post, hu8])]
    · by_cases c : iter.start.val ≤ k
      · have c' : iter1.start.val ≤ k := by omega
        simp only [c, c', if_true] at r_k ⊢
        exact r_k
      · have c' : ¬ iter1.start.val ≤ k := by omega
        simp only [c, c', if_false] at r_k ⊢
        rw [r_k]
        simp only [Std.Array.set_val_eq]; simp_lists
termination_by 3 - iter.start.val
decreasing_by scalar_tac

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_3 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 3 < 256) :
    algebra.sample_poly_vec_cbd_U2_U3U2U3 σ start_n
      ⦃ (v : Vec3) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U3U2U3
  simp only [module_lattice.algebra.Vector_BaseField_U3_Default.default_BaseField_U3BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Default.default_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  step with Sample.vec_cbd_2_3_loop_spec as ⟨v, hv⟩
  simp only [Nat.zero_le, if_true] at hv
  have hlen : v.val.length = 3 := v.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hv k (by omega)).1
  · apply Vector.ext
    intro k hk
    simp only [toPolyVec, Vector.getElem_ofFn]
    exact (hv k hk).2

theorem Sample.vec_cbd_2_4_loop_spec (iter : core.ops.range.Range Usize) (σ : Std.Array U8 32#usize)
    (start_n : U8) (a : Vec4) (h : start_n.val + 4 < 256)
    (hend : iter.end.val = 4) (hstart : iter.start.val ≤ 4) :
    algebra.sample_poly_vec_cbd_U2_U4U2U4_loop iter σ start_n a ⦃ r => ∀ k (hk : k < 4),
      if iter.start.val ≤ k then
        Coeffs.Bounded q (r.val[k]'(by grind)) ∧
        Coeffs.toPoly q (r.val[k]'(by grind)) = SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + k)))
      else r.val[k]'(by grind) = a.val[k]'(by grind) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U4U2U4_loop
  simp only [hybrid_array.Array_Polynomial_BaseField_U4_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U4Polynomial_BaseFieldUsizeU4]
  step*
  · intro k hk
    have : ¬ iter.start.val ≤ k := by split_ifs at o_post <;> (simp_all; try omega)
    simp [this]
  · have hs : iter.start.val < 4 := by split_ifs at o_post <;> simp_all
    have hi : i = iter.start := by split_ifs at o_post <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
    subst hi
    step with Sample.truncate_u8_spec as ⟨i_u8, hu8⟩
    step*
    have r_k := r_post k k_post
    rw [index_mut_Polynomial_BaseField_usize_U4_back_post] at r_k
    by_cases hk : k = iter.start.val
    · subst hk
      have : ¬ iter1.start.val ≤ iter.start.val := by omega
      simp only [this, if_false, le_refl, if_true] at r_k ⊢
      rw [r_k]
      simp only [Std.Array.set_val_eq]; simp_lists
      refine ⟨pbf_post, ?_⟩
      rw [pbf_post1, prf_output_post, Sample.toByte_eq_ofNat N _ (by rw [N_post, hu8])]
    · by_cases c : iter.start.val ≤ k
      · have c' : iter1.start.val ≤ k := by omega
        simp only [c, c', if_true] at r_k ⊢
        exact r_k
      · have c' : ¬ iter1.start.val ≤ k := by omega
        simp only [c, c', if_false] at r_k ⊢
        rw [r_k]
        simp only [Std.Array.set_val_eq]; simp_lists
termination_by 4 - iter.start.val
decreasing_by scalar_tac

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_4 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 4 < 256) :
    algebra.sample_poly_vec_cbd_U2_U4U2U4 σ start_n
      ⦃ (v : Vec4) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U2_U4U2U4
  simp only [module_lattice.algebra.Vector_BaseField_U4_Default.default_BaseField_U4BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Default.default_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  step with Sample.vec_cbd_2_4_loop_spec as ⟨v, hv⟩
  simp only [Nat.zero_le, if_true] at hv
  have hlen : v.val.length = 4 := v.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hv k (by omega)).1
  · apply Vector.ext
    intro k hk
    simp only [toPolyVec, Vector.getElem_ofFn]
    exact (hv k hk).2

theorem Sample.vec_cbd_3_2_loop_spec (iter : core.ops.range.Range Usize) (σ : Std.Array U8 32#usize)
    (start_n : U8) (a : Vec2) (h : start_n.val + 2 < 256)
    (hend : iter.end.val = 2) (hstart : iter.start.val ≤ 2) :
    algebra.sample_poly_vec_cbd_U3_U2U3U2_loop iter σ start_n a ⦃ r => ∀ k (hk : k < 2),
      if iter.start.val ≤ k then
        Coeffs.Bounded q (r.val[k]'(by grind)) ∧
        Coeffs.toPoly q (r.val[k]'(by grind)) = SamplePolyCBD (η := (η₁ .ML_KEM_512)) (PRF (η₁ .ML_KEM_512) (arrayToBytes σ) (UInt8.ofNat (start_n.val + k)))
      else r.val[k]'(by grind) = a.val[k]'(by grind) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U3_U2U3U2_loop
  simp only [hybrid_array.Array_Polynomial_BaseField_U2_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2]
  step*
  · intro k hk
    have : ¬ iter.start.val ≤ k := by split_ifs at o_post <;> (simp_all; try omega)
    simp [this]
  · have hs : iter.start.val < 2 := by split_ifs at o_post <;> simp_all
    have hi : i = iter.start := by split_ifs at o_post <;> simp_all
    have h1s : iter1.start.val = iter.start.val + 1 := by split_ifs at o_post <;> simp_all
    subst hi
    step with Sample.truncate_u8_spec as ⟨i_u8, hu8⟩
    step*
    have r_k := r_post k k_post
    rw [index_mut_Polynomial_BaseField_usize_U2_back_post] at r_k
    by_cases hk : k = iter.start.val
    · subst hk
      have : ¬ iter1.start.val ≤ iter.start.val := by omega
      simp only [this, if_false, le_refl, if_true] at r_k ⊢
      rw [r_k]
      simp only [Std.Array.set_val_eq]; simp_lists
      refine ⟨pbf_post, ?_⟩
      rw [pbf_post1, prf_output_post, Sample.toByte_eq_ofNat N _ (by rw [N_post, hu8])]
    · by_cases c : iter.start.val ≤ k
      · have c' : iter1.start.val ≤ k := by omega
        simp only [c, c', if_true] at r_k ⊢
        exact r_k
      · have c' : ¬ iter1.start.val ≤ k := by omega
        simp only [c, c', if_false] at r_k ⊢
        rw [r_k]
        simp only [Std.Array.set_val_eq]; simp_lists
termination_by 2 - iter.start.val
decreasing_by scalar_tac

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_3_2 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 2 < 256) :
    algebra.sample_poly_vec_cbd_U3_U2U3U2 σ start_n
      ⦃ (v : Vec2) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := (η₁ .ML_KEM_512)) (PRF (η₁ .ML_KEM_512) (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  unfold algebra.sample_poly_vec_cbd_U3_U2U3U2
  simp only [module_lattice.algebra.Vector_BaseField_U2_Default.default_BaseField_U2BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Default.default_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  step with Sample.vec_cbd_3_2_loop_spec as ⟨v, hv⟩
  simp only [Nat.zero_le, if_true] at hv
  have hlen : v.val.length = 2 := v.property
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hv k (by omega)).1
  · apply Vector.ext
    intro k hk
    simp only [toPolyVec, Vector.getElem_ofFn]
    exact (hv k hk).2


end MlKem.Properties
