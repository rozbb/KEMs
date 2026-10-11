import MlKem.Properties.Poly

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

-- INTERFACE
@[step] theorem ntt_spec (a : Coeffs)
    (ha : a.Bounded q) :
    algebra.Polynomial_BaseField_Ntt.ntt a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toTq = Polynomial.NTT a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_inverse_spec (a : Coeffs)
    (ha : a.Bounded q) :
    algebra.NttPolynomial_BaseField_NttInverse.ntt_inverse a
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = Tq.NTTInv a.toTq ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U2_Ntt.ntt_U2U2 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U2_NttInverse.ntt_inverse_U2U2 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U3_Ntt.ntt_U3U3 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U3_NttInverse.ntt_inverse_U3U3 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    algebra.Vector_BaseField_U4_Ntt.ntt_U4U4 v
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = PolyVector.NTT (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_inverse_vec_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    algebra.NttVector_BaseField_U4_NttInverse.ntt_inverse_U4U4 v
      ⦃ r => Vec.Bounded q r ∧ toPolyVec q r = NTTVector.NTTInv (toNTTVec v) ⦄ := by
  sorry


end MlKem.Properties
