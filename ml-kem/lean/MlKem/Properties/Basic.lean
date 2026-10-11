import ExtractedRust.Funs
import Wychelean.KEM.MLKEM.Scheme

/-! Basic definitions shared by the proofs. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)

namespace MlKem.Properties

theorem triple_means_success {α : Type} {x : Result α} {p : α → Prop} (h : x ⦃ p ⦄) :
    ∃ v, x = ok v ∧ p v := by
  cases x with
  | ret v => exact ⟨v, rfl, (WP.spec_ok v).mp h⟩
  | vis i k => exact ((WP.spec_vis i k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

/-- Converts a Rust `[u8; n]` to the spec's byte vector `ByteVec n` -/
def arrayToBytes {n : Usize} (a : Array U8 n) : ByteVec (n : ℕ) :=
  Vector.ofFn fun (i : Fin (n : ℕ)) => UInt8.ofBitVec (a.val[i.val]'(by have := a.property; grind)).bv

/-- The first half of a 64-byte seed: FIPS 203's `d`. -/
def seedD (seed : Array U8 64#usize) : ByteVec 32 := Vector.ofFn fun i => (arrayToBytes seed)[i.val]

/-- The second half of a 64-byte seed: FIPS 203's `z`. -/
def seedZ (seed : Array U8 64#usize) : ByteVec 32 := Vector.ofFn fun i =>
  (arrayToBytes seed)[32 + i.val]'(by have := i.isLt; simp; omega)

/-- Runs `f` on the result of a fallible Rust function (e.g. a deserialization) if it succeeded, and
returns `none` if it returned an error. -/
def whenOk {α ε β : Type} (r : Result (core.result.Result α ε)) (f : α → Result β) : Result (Option β) := do
  let x ← r
  match x with
  | core.result.Result.Ok a => some <$> f a
  | core.result.Result.Err _ => ok none

end MlKem.Properties
