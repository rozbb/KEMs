import MlKem.Properties.Arith

/-! # Byte encoding

Specs of `byte_encode` and `byte_decode` (Algorithms 5 and 6), and of the `Encode` impls built on
them.

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

-- INTERFACE
@[step] theorem byte_encode_spec_1 (a : Coeffs)
    (ha : a.Bounded (m 1)) :
    module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1 a
      ⦃ r => arrayToBytes r = ByteEncode 1 (a.toVector (m 1)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_encode_spec_4 (a : Coeffs)
    (ha : a.Bounded (m 4)) :
    module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4 a
      ⦃ r => arrayToBytes r = ByteEncode 4 (a.toVector (m 4)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_encode_spec_5 (a : Coeffs)
    (ha : a.Bounded (m 5)) :
    module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5 a
      ⦃ r => arrayToBytes r = ByteEncode 5 (a.toVector (m 5)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_encode_spec_10 (a : Coeffs)
    (ha : a.Bounded (m 10)) :
    module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10 a
      ⦃ r => arrayToBytes r = ByteEncode 10 (a.toVector (m 10)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_encode_spec_11 (a : Coeffs)
    (ha : a.Bounded (m 11)) :
    module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11 a
      ⦃ r => arrayToBytes r = ByteEncode 11 (a.toVector (m 11)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_encode_spec_12 (a : Coeffs)
    (ha : a.Bounded (m 12)) :
    module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12 a
      ⦃ r => arrayToBytes r = ByteEncode 12 (a.toVector (m 12)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_1 (b : Std.Array U8 32#usize) :
    module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1 b
      ⦃ (r : Coeffs) => r.Bounded (m 1) ∧ r.toVector (m 1) = ByteDecode (d := 1) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_4 (b : Std.Array U8 128#usize) :
    module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4 b
      ⦃ (r : Coeffs) => r.Bounded (m 4) ∧ r.toVector (m 4) = ByteDecode (d := 4) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_5 (b : Std.Array U8 160#usize) :
    module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5 b
      ⦃ (r : Coeffs) => r.Bounded (m 5) ∧ r.toVector (m 5) = ByteDecode (d := 5) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_6 (b : Std.Array U8 192#usize) :
    module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6 b
      ⦃ (r : Coeffs) => r.Bounded (m 6) ∧ r.toVector (m 6) = ByteDecode (d := 6) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_10 (b : Std.Array U8 320#usize) :
    module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10 b
      ⦃ (r : Coeffs) => r.Bounded (m 10) ∧ r.toVector (m 10) = ByteDecode (d := 10) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_11 (b : Std.Array U8 352#usize) :
    module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11 b
      ⦃ (r : Coeffs) => r.Bounded (m 11) ∧ r.toVector (m 11) = ByteDecode (d := 11) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem byte_decode_spec_12 (b : Std.Array U8 384#usize) :
    module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12 b
      ⦃ (r : Coeffs) => r.Bounded (m 12) ∧ r.toVector (m 12) = ByteDecode (d := 12) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_encode_spec_1 (a : Coeffs)
    (ha : a.Bounded (m 1)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U1.encode_BaseField_U1BaseFieldU1 a
      ⦃ r => arrayToBytes r = ByteEncode 1 (a.toVector (m 1)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_encode_spec_4 (a : Coeffs)
    (ha : a.Bounded (m 4)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U4.encode_BaseField_U4BaseFieldU4 a
      ⦃ r => arrayToBytes r = ByteEncode 4 (a.toVector (m 4)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_encode_spec_5 (a : Coeffs)
    (ha : a.Bounded (m 5)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U5.encode_BaseField_U5BaseFieldU5 a
      ⦃ r => arrayToBytes r = ByteEncode 5 (a.toVector (m 5)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_encode_spec_10 (a : Coeffs)
    (ha : a.Bounded (m 10)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U10.encode_BaseField_U10BaseFieldU10 a
      ⦃ r => arrayToBytes r = ByteEncode 10 (a.toVector (m 10)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_encode_spec_11 (a : Coeffs)
    (ha : a.Bounded (m 11)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U11.encode_BaseField_U11BaseFieldU11 a
      ⦃ r => arrayToBytes r = ByteEncode 11 (a.toVector (m 11)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_1 (b : Std.Array U8 32#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U1.decode_BaseField_U1BaseFieldU1 b
      ⦃ (r : Coeffs) => r.Bounded (m 1) ∧ r.toVector (m 1) = ByteDecode (d := 1) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_4 (b : Std.Array U8 128#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U4.decode_BaseField_U4BaseFieldU4 b
      ⦃ (r : Coeffs) => r.Bounded (m 4) ∧ r.toVector (m 4) = ByteDecode (d := 4) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_5 (b : Std.Array U8 160#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U5.decode_BaseField_U5BaseFieldU5 b
      ⦃ (r : Coeffs) => r.Bounded (m 5) ∧ r.toVector (m 5) = ByteDecode (d := 5) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_6 (b : Std.Array U8 192#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U6.decode_BaseField_U6BaseFieldU6 b
      ⦃ (r : Coeffs) => r.Bounded (m 6) ∧ r.toVector (m 6) = ByteDecode (d := 6) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_10 (b : Std.Array U8 320#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U10.decode_BaseField_U10BaseFieldU10 b
      ⦃ (r : Coeffs) => r.Bounded (m 10) ∧ r.toVector (m 10) = ByteDecode (d := 10) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem poly_decode_spec_11 (b : Std.Array U8 352#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U11.decode_BaseField_U11BaseFieldU11 b
      ⦃ (r : Coeffs) => r.Bounded (m 11) ∧ r.toVector (m 11) = ByteDecode (d := 11) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_poly_encode_spec_12 (a : Coeffs)
    (ha : a.Bounded q) :
    module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.encode_BaseField_U12BaseFieldU12 a
      ⦃ r => arrayToBytes r = ByteEncode 12 (a.toVector q) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_poly_decode_spec_12 (b : Std.Array U8 384#usize) :
    module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.decode_BaseField_U12BaseFieldU12 b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q = ByteDecode (d := 12) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_encode_spec_2 (v : Vec2)
    (hv : Vec.Bounded (m 10) v) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.encode_BaseField_U10_U2BaseFieldU10U2 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_512) 10 (toPolyVec (m 10) v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decode_spec_2 (b : Std.Array U8 640#usize) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.decode_BaseField_U10_U2BaseFieldU10U2 b
      ⦃ r => Vec.Bounded (m 10) r ∧ toPolyVec (m 10) r = PolyVector.ByteDecode (k := k .ML_KEM_512) 10 (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_encode_spec_3 (v : Vec3)
    (hv : Vec.Bounded (m 10) v) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.encode_BaseField_U10_U3BaseFieldU10U3 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_768) 10 (toPolyVec (m 10) v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decode_spec_3 (b : Std.Array U8 960#usize) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.decode_BaseField_U10_U3BaseFieldU10U3 b
      ⦃ r => Vec.Bounded (m 10) r ∧ toPolyVec (m 10) r = PolyVector.ByteDecode (k := k .ML_KEM_768) 10 (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_encode_spec_4 (v : Vec4)
    (hv : Vec.Bounded (m 11) v) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.encode_BaseField_U11_U4BaseFieldU11U4 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_1024) 11 (toPolyVec (m 11) v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem vec_decode_spec_4 (b : Std.Array U8 1408#usize) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.decode_BaseField_U11_U4BaseFieldU11U4 b
      ⦃ r => Vec.Bounded (m 11) r ∧ toPolyVec (m 11) r = PolyVector.ByteDecode (k := k .ML_KEM_1024) 11 (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.encode_BaseField_U12_U2BaseFieldU12U2 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_512) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_2 (b : Std.Array U8 768#usize) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.decode_BaseField_U12_U2BaseFieldU12U2 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_512) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem encode_u12_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    param.MlKem512_PkeParams.encode_u12_MlKem512MlKem512 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_512) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem decode_u12_spec_2 (b : Std.Array U8 768#usize) :
    param.MlKem512_PkeParams.decode_u12_MlKem512MlKem512 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_512) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.encode_BaseField_U12_U3BaseFieldU12U3 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_768) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_3 (b : Std.Array U8 1152#usize) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.decode_BaseField_U12_U3BaseFieldU12U3 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_768) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem encode_u12_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    param.MlKem768_PkeParams.encode_u12_MlKem768MlKem768 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_768) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem decode_u12_spec_3 (b : Std.Array U8 1152#usize) :
    param.MlKem768_PkeParams.decode_u12_MlKem768MlKem768 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_768) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.encode_BaseField_U12_U4BaseFieldU12U4 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_1024) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_4 (b : Std.Array U8 1536#usize) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.decode_BaseField_U12_U4BaseFieldU12U4 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_1024) (arrayToBytes b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem encode_u12_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    param.MlKem1024_PkeParams.encode_u12_MlKem1024MlKem1024 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_1024) (toNTTVec v) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem decode_u12_spec_4 (b : Std.Array U8 1536#usize) :
    param.MlKem1024_PkeParams.decode_u12_MlKem1024MlKem1024 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_1024) (arrayToBytes b) ⦄ := by
  sorry


end MlKem.Properties
