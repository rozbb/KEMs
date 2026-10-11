import MlKem.Properties.Defs

/-! # Field arithmetic

Specs of the `u16` field arithmetic of `module_lattice::algebra::Elem<BaseField>`: `small_reduce`
(conditional subtraction), `barrett_reduce`, and the `Add`, `Sub` and `Mul` impls. -/

open Aeneas Aeneas.Std Result
open RustMlKem

namespace MlKem.Properties

/-! ## The models of the `core` integer operations the extracted code calls -/

@[step] theorem u16_add_spec (x y : U16) (h : x.val + y.val ≤ U16.max) :
    U16.Insts.CoreOpsArithAddU16.add x y ⦃ r => r.val = x.val + y.val ⦄ := by
  unfold U16.Insts.CoreOpsArithAddU16.add; step*

@[step] theorem u16_sub_spec (x y : U16) (h : y.val ≤ x.val) :
    U16.Insts.CoreOpsArithSubU16.sub x y ⦃ r => r.val = x.val - y.val ⦄ := by
  unfold U16.Insts.CoreOpsArithSubU16.sub; step*

@[step] theorem u32_mul_spec (x y : U32) (h : x.val * y.val ≤ U32.max) :
    U32.Insts.CoreOpsArithMulU32.mul x y ⦃ r => r.val = x.val * y.val ⦄ := by
  unfold U32.Insts.CoreOpsArithMulU32.mul; step*

@[step] theorem u16_into_u32_spec (x : U16) :
    U16.Insts.CoreConvertIntoU32.into x ⦃ r => r.val = x.val ⦄ := by
  simp [U16.Insts.CoreConvertIntoU32.into]

@[step] theorem u32_into_u64_spec (x : U32) :
    U32.Insts.CoreConvertIntoU64.into x ⦃ r => r.val = x.val ⦄ := by
  simp [U32.Insts.CoreConvertIntoU64.into]

@[step] theorem wrapping_neg_spec (x : U16) :
    core.num.U16.wrapping_neg x ⦃ r => r.val = (2 ^ 16 - x.val) % 2 ^ 16 ⦄ := by
  simp only [core.num.U16.wrapping_neg, WP.spec_ok]
  change (-x.bv).toNat = (2 ^ 16 - x.bv.toNat) % 2 ^ 16
  rw [BitVec.toNat_neg]

/-! ## Constants -/

@[simp] theorem Q_val : algebra.BaseField_Field.Q.val = 3329 := by
  simp [algebra.BaseField_Field.Q]

@[simp] theorem QLL_val : algebra.BaseField_Field.QLL.val = 3329 := by
  simp [algebra.BaseField_Field.QLL]

@[step] theorem BARRETT_SHIFT_spec : algebra.BaseField_Field.BARRETT_SHIFT ⦃ r => r.val = 24 ⦄ := by
  have hlog : Nat.log2 3329 = 11 := (Nat.log2_eq_iff (by decide)).mpr ⟨by decide, by decide⟩
  unfold algebra.BaseField_Field.BARRETT_SHIFT core.num.U16.ilog2
  simp only [Q_val, show (3329 = 0) = False by decide, if_false, hlog]
  have h11 : (⟨BitVec.ofNat 32 11⟩ : U32).val = 11 := rfl
  have hnb : (12 : Nat) % 2 ^ System.Platform.numBits = 12 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  let* ⟨ i1, hi1 ⟩ ← U32.add_spec
  rw [h11] at hi1; clear h11
  step*

@[step] theorem BARRETT_MULTIPLIER_spec :
    algebra.BaseField_Field.BARRETT_MULTIPLIER ⦃ r => r.val = 5039 ⦄ := by
  unfold algebra.BaseField_Field.BARRETT_MULTIPLIER
  step*
  · simp
  · simp_all [Nat.shiftLeft_eq, U64.size, U64.numBits]

/-! ## Reductions -/

@[step] theorem small_reduce_spec (x : U16) (h : x.val < 2 * 3329) :
    algebra.BaseField_Field.small_reduce x ⦃ r => r.val = x.val % 3329 ⦄ := by
  unfold algebra.BaseField_Field.small_reduce
  step*
  all_goals
    have hi1 : i1.val = if x.val ≥ 3329 then 3329 else 0 := by
      have : i1.val = 3329 &&& mask.val := by
        simp only [UScalar.val, i1_post1, BitVec.toNat_and]
        rw [show algebra.BaseField_Field.Q.bv.toNat = 3329 from Q_val]
      rw [this, mask_post, i_post]
      have : (x ≥ algebra.BaseField_Field.Q) ↔ x.val ≥ 3329 := by
        simp [UScalar.le_equiv]
      by_cases hx : x.val ≥ 3329 <;> simp [hx, this]
    split at hi1 <;> omega

@[step] theorem truncate_u64_u16_spec (x : U64) (h : x.val < 2 ^ 16) :
    module_lattice.truncate.u16_Truncate_u64.truncate x ⦃ r => r.val = x.val ⦄ := by
  unfold module_lattice.truncate.u16_Truncate_u64.truncate
  simp [lift, U16.rMax]
  rw [show (65535 : Nat) = 2^16 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The Barrett remainder `x - ⌊x * 5039 / 2^24⌋ * 3329` lies in `[0, 2 * 3329)` for `x < 2^24`. -/
theorem barrett_bound (x : Nat) (h : x < 2 ^ 24) :
    x * 5039 / 2 ^ 24 * 3329 ≤ x ∧ x - x * 5039 / 2 ^ 24 * 3329 < 2 * 3329 := by
  omega

/-- Barrett reduction, for the inputs it sees: products of two reduced field elements. -/
@[step] theorem barrett_reduce_spec (x : U32) (h : x.val < 2 ^ 24) :
    algebra.BaseField_Field.barrett_reduce x ⦃ r => r.val = x.val % 3329 ⦄ := by
  unfold algebra.BaseField_Field.barrett_reduce
  step*
  all_goals
    have hq : quotient.val = x.val * 5039 / 2 ^ 24 := by
      rw [quotient_post, Nat.shiftRight_eq_div_pow, product_post, x1_post, i_post, i1_post]
    have hb := barrett_bound x.val h
    simp only [QLL_val] at *
    first
    | (rw [hq]; scalar_tac)
    | omega

/-! ## The field operations -/

-- INTERFACE
@[step] theorem elem_add_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val + b.val) % 3329 ⦄ := by
  unfold module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField
  step*

-- INTERFACE
@[step] theorem elem_sub_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val + 3329 - b.val) % 3329 ⦄ := by
  unfold module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField
  step* <;> simp only [Q_val] at * <;> scalar_tac

-- INTERFACE
@[step] theorem elem_mul_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val * b.val) % 3329 ⦄ := by
  unfold module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField
  step*

end MlKem.Properties
