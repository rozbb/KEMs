import MlKem.Properties.Arith

/-! # Compression

Specs of `Compress for Polynomial` and `Compress for Vector` (§4.2.1, Eqs. 4.7 and 4.8).

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

-- INTERFACE
@[step] theorem poly_compress_spec_1 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U1U1 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 1) ∧ r'.toPoly (m 1) = Polynomial.Compress 1 a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decompress_spec_1 (a : Coeffs)
    (ha : a.Bounded (2 ^ 1)) :
    compress.Polynomial_BaseField_Compress.decompress_U1U1 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 1 (a.toPoly (m 1)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_compress_spec_4 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U4U4 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 4) ∧ r'.toPoly (m 4) = Polynomial.Compress 4 a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decompress_spec_4 (a : Coeffs)
    (ha : a.Bounded (2 ^ 4)) :
    compress.Polynomial_BaseField_Compress.decompress_U4U4 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 4 (a.toPoly (m 4)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_compress_spec_5 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U5U5 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 5) ∧ r'.toPoly (m 5) = Polynomial.Compress 5 a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decompress_spec_5 (a : Coeffs)
    (ha : a.Bounded (2 ^ 5)) :
    compress.Polynomial_BaseField_Compress.decompress_U5U5 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 5 (a.toPoly (m 5)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_compress_spec_10 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U10U10 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 10) ∧ r'.toPoly (m 10) = Polynomial.Compress 10 a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decompress_spec_10 (a : Coeffs)
    (ha : a.Bounded (2 ^ 10)) :
    compress.Polynomial_BaseField_Compress.decompress_U10U10 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 10 (a.toPoly (m 10)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_compress_spec_11 (a : Coeffs)
    (ha : a.Bounded q) :
    compress.Polynomial_BaseField_Compress.compress_U11U11 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded (2 ^ 11) ∧ r'.toPoly (m 11) = Polynomial.Compress 11 a.toPoly ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decompress_spec_11 (a : Coeffs)
    (ha : a.Bounded (2 ^ 11)) :
    compress.Polynomial_BaseField_Compress.decompress_U11U11 a
      ⦃ (r r' : Coeffs) => r = r' ∧ r'.Bounded q ∧ r'.toPoly = Polynomial.Decompress 11 (a.toPoly (m 11)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_compress_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U2_Compress.compress_U2_U10U2U10 v
      ⦃ (r r' : Vec2) => r = r' ∧ Vec.Bounded (2 ^ 10) r' ∧ toPolyVec (m 10) r' = PolyVector.Compress (k := k .ML_KEM_512) 10 (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decompress_spec_2 (v : Vec2)
    (hv : Vec.Bounded (2 ^ 10) v) :
    compress.Vector_BaseField_U2_Compress.decompress_U2_U10U2U10 v
      ⦃ (r r' : Vec2) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_512) 10 (toPolyVec (m 10) v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_compress_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U3_Compress.compress_U3_U10U3U10 v
      ⦃ (r r' : Vec3) => r = r' ∧ Vec.Bounded (2 ^ 10) r' ∧ toPolyVec (m 10) r' = PolyVector.Compress (k := k .ML_KEM_768) 10 (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decompress_spec_3 (v : Vec3)
    (hv : Vec.Bounded (2 ^ 10) v) :
    compress.Vector_BaseField_U3_Compress.decompress_U3_U10U3U10 v
      ⦃ (r r' : Vec3) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_768) 10 (toPolyVec (m 10) v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_compress_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    compress.Vector_BaseField_U4_Compress.compress_U4_U11U4U11 v
      ⦃ (r r' : Vec4) => r = r' ∧ Vec.Bounded (2 ^ 11) r' ∧ toPolyVec (m 11) r' = PolyVector.Compress (k := k .ML_KEM_1024) 11 (toPolyVec q v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decompress_spec_4 (v : Vec4)
    (hv : Vec.Bounded (2 ^ 11) v) :
    compress.Vector_BaseField_U4_Compress.decompress_U4_U11U4U11 v
      ⦃ (r r' : Vec4) => r = r' ∧ Vec.Bounded q r' ∧ toPolyVec q r' = PolyVector.Decompress (k := k .ML_KEM_1024) 11 (toPolyVec (m 11) v) ⦄ := by
  sorry


end MlKem.Properties
