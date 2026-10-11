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
  sorry

@[step] theorem BARRETT_MULTIPLIER_spec :
    algebra.BaseField_Field.BARRETT_MULTIPLIER ⦃ r => r.val = 5039 ⦄ := by
  unfold algebra.BaseField_Field.BARRETT_MULTIPLIER
  sorry

/-! ## Reductions -/

@[step] theorem small_reduce_spec (x : U16) (h : x.val < 2 * 3329) :
    algebra.BaseField_Field.small_reduce x ⦃ r => r.val = x.val % 3329 ⦄ := by
  unfold algebra.BaseField_Field.small_reduce
  step*
  all_goals sorry

@[step] theorem truncate_u64_u16_spec (x : U64) (h : x.val < 2 ^ 16) :
    module_lattice.truncate.u16_Truncate_u64.truncate x ⦃ r => r.val = x.val ⦄ := by
  unfold module_lattice.truncate.u16_Truncate_u64.truncate
  step*
  all_goals sorry

/-- Barrett reduction, for the inputs it sees: products of two reduced field elements. -/
@[step] theorem barrett_reduce_spec (x : U32) (h : x.val < 2 ^ 24) :
    algebra.BaseField_Field.barrett_reduce x ⦃ r => r.val = x.val % 3329 ⦄ := by
  unfold algebra.BaseField_Field.barrett_reduce
  step*
  all_goals sorry

/-! ## The field operations -/

-- INTERFACE
@[step] theorem elem_add_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Add_Elem_BaseField.add_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val + b.val) % 3329 ⦄ := by
  sorry

-- INTERFACE
@[step] theorem elem_sub_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Sub_Elem_BaseField.sub_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val + 3329 - b.val) % 3329 ⦄ := by
  sorry

-- INTERFACE
@[step] theorem elem_mul_spec (a b : U16) (ha : a.val < 3329) (hb : b.val < 3329) :
    module_lattice.algebra.Elem_BaseField_Mul_Elem_BaseField.mul_BaseFieldBaseField a b
      ⦃ r => r.val = (a.val * b.val) % 3329 ⦄ := by
  sorry

end MlKem.Properties
