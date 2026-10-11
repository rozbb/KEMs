import MlKem.Properties.Defs

/-! # Hash functions

Specs of `G`, `H`, `J`, `PRF` and `XOF` (§4.1). Given the models of the `sha3` and `shake` crates in
`ExtractedRust/FunsExternal.lean`, these say that `ml_kem::crypto` uses them as the spec does.

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

namespace MlKem.Properties

-- INTERFACE
@[step] theorem G_spec (x y : Slice U8) :
    crypto.G x y
      ⦃ (a b : Std.Array U8 32#usize) => (arrayToBytes a, arrayToBytes b) = G (bytesOfList (x.val ++ y.val)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem H_spec_800 (x : Std.Array U8 800#usize) :
    crypto.H_Array_u8_U800Array_u8_U800 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem H_spec_1184 (x : Std.Array U8 1184#usize) :
    crypto.H_Array_u8_U1184Array_u8_U1184 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem H_spec_1568 (x : Std.Array U8 1568#usize) :
    crypto.H_Array_u8_U1568Array_u8_U1568 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem J_spec (x y : Slice U8) :
    crypto.J x y
      ⦃ r => arrayToBytes r = J (bytesOfList (x.val ++ y.val)) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem PRF_spec_2 (s : Std.Array U8 32#usize) (b : U8) :
    crypto.PRF_U2U2 s b
      ⦃ r => arrayToBytes r = PRF η₂ (arrayToBytes s) (toByte b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem PRF_spec_3 (s : Std.Array U8 32#usize) (b : U8) :
    crypto.PRF_U3U3 s b
      ⦃ r => arrayToBytes r = PRF (η₁ .ML_KEM_512) (arrayToBytes s) (toByte b) ⦄ := by
  sorry

-- INTERFACE
@[step] theorem XOF_spec (ρ : Std.Array U8 32#usize) (i j : U8) :
    crypto.XOF ρ i j
      ⦃ r => r = XOF.Finalize (XOF.Absorb XOF.Init (arrayToBytes ρ ++ #v[toByte i, toByte j])) ⦄ := by
  sorry


end MlKem.Properties
