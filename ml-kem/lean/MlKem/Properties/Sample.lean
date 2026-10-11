import MlKem.Properties.Hash
import MlKem.Properties.Encode

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

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_2 (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U2U2 ρ transpose
      ⦃ (A : Mat2) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 2 (arrayToBytes ρ)) else sampleMatrix 2 (arrayToBytes ρ) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_3 (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U3U3 ρ transpose
      ⦃ (A : Mat3) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 3 (arrayToBytes ρ)) else sampleMatrix 3 (arrayToBytes ρ) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem matrix_sample_ntt_spec_4 (ρ : Std.Array U8 32#usize) (transpose : Bool) :
    algebra.matrix_sample_ntt_U4U4 ρ transpose
      ⦃ (A : Mat4) => Mat.Bounded q A ∧ toNTTMat A = if transpose then Wychelean.Utils.Linear.Mat.transpose (sampleMatrix 4 (arrayToBytes ρ)) else sampleMatrix 4 (arrayToBytes ρ) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_cbd_spec_2 (B : Std.Array U8 128#usize) :
    algebra.sample_poly_cbd_U2U2 B
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = SamplePolyCBD (η := η₂) (arrayToBytes B) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_cbd_spec_3 (B : Std.Array U8 192#usize) :
    algebra.sample_poly_cbd_U3U3 B
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toPoly = SamplePolyCBD (η := η₁ .ML_KEM_512) (arrayToBytes B) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_2 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 2 < 256) :
    algebra.sample_poly_vec_cbd_U2_U2U2U2 σ start_n
      ⦃ (v : Vec2) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_3 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 3 < 256) :
    algebra.sample_poly_vec_cbd_U2_U3U2U3 σ start_n
      ⦃ (v : Vec3) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_2_4 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 4 < 256) :
    algebra.sample_poly_vec_cbd_U2_U4U2U4 σ start_n
      ⦃ (v : Vec4) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := η₂) (PRF η₂ (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem sample_poly_vec_cbd_spec_3_2 (σ : Std.Array U8 32#usize) (start_n : U8)
    (h : start_n.val + 2 < 256) :
    algebra.sample_poly_vec_cbd_U3_U2U3U2 σ start_n
      ⦃ (v : Vec2) => Vec.Bounded q v ∧ toPolyVec q v = Vector.ofFn fun i => SamplePolyCBD (η := (η₁ .ML_KEM_512)) (PRF (η₁ .ML_KEM_512) (arrayToBytes σ) (UInt8.ofNat (start_n.val + i.val))) ⦄ := by
  sorry


end MlKem.Properties
