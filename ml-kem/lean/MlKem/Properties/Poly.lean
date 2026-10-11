import MlKem.Properties.Arith

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

-- INTERFACE
@[step] theorem poly_add_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefPolynomial_BaseField_Add_RefPolynomial_BaseField.add_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = a.toPoly + b.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_sub_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefPolynomial_BaseField_Sub_RefPolynomial_BaseField.sub_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = a.toPoly - b.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem elem_mul_poly_spec (c : U16) (a : Coeffs)
    (hc : c.val < q) (ha : a.Bounded q) :
    module_lattice.algebra.Elem_BaseField_Mul_RefPolynomial_BaseField.mul_BaseFieldBaseField c a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q = toZq c • a.toVector q ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_poly_add_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefNttPolynomial_BaseField_Add_RefNttPolynomial_BaseField.add_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq + b.toTq ⦄ := by
  sorry

-- INTERFACE
@[step] theorem multiply_ntt_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    algebra.BaseField_MultiplyNtt.multiply_ntt a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq * b.toTq ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_poly_mul_spec (a b : Coeffs)
    (ha : a.Bounded q) (hb : b.Bounded q) :
    module_lattice.algebra.RefNttPolynomial_BaseField_Mul_RefNttPolynomial_BaseField.mul_BaseFieldBaseField a b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = a.toTq * b.toTq ⦄ := by
  sorry

/-! ### Rank 2 -/

-- INTERFACE
@[step] theorem vec_add_ref_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U2_Add_RefVector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_add_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U2_Add_Vector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_add_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Add_RefNttVector_BaseField_U2.add_BaseField_U2BaseFieldU2 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_dot_spec_2 (v : Vec2) (w : Vec2)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2BaseFieldU2 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_2 (A : Mat2) (v : Vec2)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U2_U2_Mul_RefNttVector_BaseField_U2.mul_BaseField_U2_U2BaseFieldU2U2 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  sorry

/-! ### Rank 3 -/

-- INTERFACE
@[step] theorem vec_add_ref_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U3_Add_RefVector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_add_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U3_Add_Vector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_add_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Add_RefNttVector_BaseField_U3.add_BaseField_U3BaseFieldU3 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_dot_spec_3 (v : Vec3) (w : Vec3)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3BaseFieldU3 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_3 (A : Mat3) (v : Vec3)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U3_U3_Mul_RefNttVector_BaseField_U3.mul_BaseField_U3_U3BaseFieldU3U3 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  sorry

/-! ### Rank 4 -/

-- INTERFACE
@[step] theorem vec_add_ref_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefVector_BaseField_U4_Add_RefVector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_add_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.Vector_BaseField_U4_Add_Vector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = toPolyVec q v + toPolyVec q w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_add_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Add_RefNttVector_BaseField_U4.add_BaseField_U4BaseFieldU4 v w
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = toNTTVec v + toNTTVec w ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_dot_spec_4 (v : Vec4) (w : Vec4)
    (hv : Vec.Bounded q v) (hw : Vec.Bounded q w) :
    module_lattice.algebra.RefNttVector_BaseField_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4BaseFieldU4 v w
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Wychelean.Utils.Linear.innerProduct (toNTTVec v) (toNTTVec w) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_mat_mul_spec_4 (A : Mat4) (v : Vec4)
    (hA : Mat.Bounded q A) (hv : Vec.Bounded q v) :
    module_lattice.algebra.RefNttMatrix_BaseField_U4_U4_Mul_RefNttVector_BaseField_U4.mul_BaseField_U4_U4BaseFieldU4U4 A v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = Wychelean.Utils.Linear.Mat.mulVec (toNTTMat A) (toNTTVec v) ⦄ := by
  sorry


end MlKem.Properties
