import MlKem.Properties.Basic

/-! # Abstraction functions

How we read the Rust values as values of the spec. Rust stores field elements as `u16`s, polynomials
(in either domain) as arrays of 256 of them, vectors as arrays of polynomials, and byte strings as
arrays of `u8`s. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM

namespace MlKem.Properties

/-- Matrices over `T_q` of any dimensions (the spec's `NTTMatrix k` is the square case). -/
abbrev NTTMatrix' (k l : ℕ) := Wychelean.Utils.Linear.Mat Tq k l

/-- The Rust type of a polynomial's coefficients, in either domain. -/
abbrev Coeffs := Std.Array U16 256#usize

/-- Rust vectors and matrices of polynomials, at the ranks of the parameter sets. (Naming these
types also avoids a Lean elaboration issue with `k#usize` literals repeated in a statement.) -/
abbrev Vec2 := Std.Array Coeffs 2#usize
abbrev Vec3 := Std.Array Coeffs 3#usize
abbrev Vec4 := Std.Array Coeffs 4#usize
abbrev Mat2 := Std.Array Vec2 2#usize
abbrev Mat3 := Std.Array Vec3 3#usize
abbrev Mat4 := Std.Array Vec4 4#usize

/-- A `u16` as an element of `ℤ_m`. -/
def toZMod (m : ℕ) (x : U16) : ZMod m := (x.val : ZMod m)

/-- A `u16` as a field element. -/
abbrev toZq (x : U16) : Zq := toZMod q x

/-- Every coefficient is a canonical representative of `ℤ_m`. -/
def Coeffs.Bounded (m : ℕ) (a : Coeffs) : Prop := ∀ x ∈ a.val, x.val < m

/-- The coefficients of a Rust polynomial, as elements of `ℤ_m`. -/
def Coeffs.toVector (m : ℕ) (a : Coeffs) : Vector (ZMod m) 256 :=
  Vector.ofFn fun i => toZMod m (a.val[i.val]'(by have := a.property; grind))

/-- A Rust polynomial as a polynomial of the spec, with coefficients in `ℤ_m`. -/
def Coeffs.toPoly (m : ℕ := q) (a : Coeffs) : Wychelean.KEM.MLKEM.Polynomial m := ⟨a.toVector m⟩

/-- A Rust NTT-domain polynomial as an element of `T_q`. -/
def Coeffs.toTq (a : Coeffs) : Tq := ⟨a.toVector q⟩

/-- A Rust vector of polynomials as a vector of the spec. -/
def toPolyVec (m : ℕ := q) {n : Usize} (v : Std.Array Coeffs n) : Vector (Wychelean.KEM.MLKEM.Polynomial m) n.val :=
  Vector.ofFn fun i => (v.val[i.val]'(by have := v.property; grind)).toPoly m

/-- A Rust vector of NTT-domain polynomials as a vector of the spec. -/
def toNTTVec {n : Usize} (v : Std.Array Coeffs n) : Vector Tq n.val :=
  Vector.ofFn fun i => (v.val[i.val]'(by have := v.property; grind)).toTq

/-- Every polynomial of a Rust vector is `Bounded m`. -/
def Vec.Bounded (m : ℕ) {n : Usize} (v : Std.Array Coeffs n) : Prop := ∀ a ∈ v.val, a.Bounded m

/-- Every polynomial of a Rust matrix is `Bounded m`. -/
def Mat.Bounded (m : ℕ) {k l : Usize} (A : Std.Array (Std.Array Coeffs l) k) : Prop :=
  ∀ row ∈ A.val, Vec.Bounded m row

/-- A Rust matrix of NTT-domain polynomials (a vector of rows) as a matrix of the spec. -/
def toNTTMat {k l : Usize} (A : Std.Array (Std.Array Coeffs l) k) : NTTMatrix' k.val l.val :=
  Vector.ofFn fun i => toNTTVec (A.val[i.val]'(by have := A.property; grind))

/-- The matrix `Â` of K-PKE.KeyGen (Algorithm 13, steps 3–7): `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`. -/
def sampleMatrix (k : ℕ) (ρ : ByteVec 32) : NTTMatrix' k k :=
  Vector.ofFn fun i => Vector.ofFn fun j => SampleNTT (ρ ++ #v[UInt8.ofNat j.val, UInt8.ofNat i.val])

/-- A Rust byte as a byte of the spec. -/
def toByte (x : U8) : Wychelean.Byte := UInt8.ofBitVec x.bv

/-- A list of Rust bytes as a byte string of the spec. -/
def bytesOfList (l : List U8) : ByteVec l.length := Vector.ofFn fun i => toByte l[i]

end MlKem.Properties
