import MlKem

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM (ParameterSet KeyGen Encaps Decaps)
open RustMlKem

namespace MlKem.TopLevel

set_option maxRecDepth 8000

/-- We introduce the `⦃ … ⦄` postcondition notation. Whenever we use this, it means the computation
succeeds (no panic or UB), and has the property defined by `p`. This theorem isn't strictly
necessary, but it demonstrates the notation. -/
theorem triple_means_success {α : Type} {x : Result α} {p : α → Prop} (h : x ⦃ p ⦄) :
    ∃ v, x = ok v ∧ p v :=
  MlKem.Properties.triple_means_success h

/-- Converts a Rust `[u8; n]` to the spec's byte vector `ByteVec n` -/
def arrayToBytes {n : Usize} (a : Array U8 n) : ByteVec (n : ℕ) :=
  Vector.ofFn fun (i : Fin (n : ℕ)) => UInt8.ofBitVec (a.val[i.val]'(by have := a.property; grind)).bv

/-- The first half of a 64-byte seed: FIPS 203's `d`. -/
def seedD (seed : Array U8 64#usize) : ByteVec 32 := Vector.ofFn fun i => (arrayToBytes seed)[i.val]

/-- The second half of a 64-byte seed: FIPS 203's `z`. -/
def seedZ (seed : Array U8 64#usize) : ByteVec 32 := Vector.ofFn fun i =>
  (arrayToBytes seed)[32 + i.val]'(by have := i.isLt; simp; omega)

/-- The three parameter sets, as an index to quantify over. -/
inductive Size | k512 | k768 | k1024

namespace Size

/-- The spec's name for the parameter set. -/
def ps : Size → ParameterSet
  | .k512 => .ML_KEM_512 | .k768 => .ML_KEM_768 | .k1024 => .ML_KEM_1024
/-- Serialized encapsulation key, in bytes. -/
def ekLen : Size → Usize | .k512 => 800#usize | .k768 => 1184#usize | .k1024 => 1568#usize
/-- Ciphertext, in bytes. -/
def ctLen : Size → Usize | .k512 => 768#usize | .k768 => 1088#usize | .k1024 => 1568#usize

/-- The Rust type `DecapsulationKey<P>` at each size. -/
def DK : Size → Type
  | .k512 => decapsulation_key.DecapsulationKey_MlKem512
  | .k768 => decapsulation_key.DecapsulationKey_MlKem768
  | .k1024 => decapsulation_key.DecapsulationKey_MlKem1024
/-- The Rust type `EncapsulationKey<P>` at each size. -/
def EK : Size → Type
  | .k512 => encapsulation_key.EncapsulationKey_MlKem512
  | .k768 => encapsulation_key.EncapsulationKey_MlKem768
  | .k1024 => encapsulation_key.EncapsulationKey_MlKem1024

/-- `DecapsulationKey::from_seed` at each size. -/
def fromSeed : (s : Size) → Array U8 64#usize → Result s.DK
  | .k512 => aeneas_entry.ml_kem_512.from_seed
  | .k768 => aeneas_entry.ml_kem_768.from_seed
  | .k1024 => aeneas_entry.ml_kem_1024.from_seed

/-- `DecapsulationKey::to_seed` at each size. -/
def toSeed : (s : Size) → s.DK → Result (Option (Array U8 64#usize))
  | .k512 => aeneas_entry.ml_kem_512.to_seed
  | .k768 => aeneas_entry.ml_kem_768.to_seed
  | .k1024 => aeneas_entry.ml_kem_1024.to_seed

/-- `DecapsulationKey::encapsulation_key` at each size. -/
def encapsulationKey : (s : Size) → s.DK → Result s.EK
  | .k512 => aeneas_entry.ml_kem_512.encapsulation_key
  | .k768 => aeneas_entry.ml_kem_768.encapsulation_key
  | .k1024 => aeneas_entry.ml_kem_1024.encapsulation_key

/-- `EncapsulationKey::new` (deserialization) at each size. -/
def ekFromBytes : (s : Size) → Array U8 s.ekLen → Result (core.result.Result s.EK crypto_common.InvalidKey)
  | .k512 => aeneas_entry.ml_kem_512.ek_from_bytes
  | .k768 => aeneas_entry.ml_kem_768.ek_from_bytes
  | .k1024 => aeneas_entry.ml_kem_1024.ek_from_bytes

/-- `EncapsulationKey::to_bytes` at each size. -/
def ekToBytes : (s : Size) → s.EK → Result (Array U8 s.ekLen)
  | .k512 => aeneas_entry.ml_kem_512.ek_to_bytes
  | .k768 => aeneas_entry.ml_kem_768.ek_to_bytes
  | .k1024 => aeneas_entry.ml_kem_1024.ek_to_bytes

/-- `EncapsulationKey::encapsulate_deterministic` at each size. -/
def encapsulate : (s : Size) → s.EK → Array U8 32#usize → Result (Array U8 s.ctLen × Array U8 32#usize)
  | .k512 => aeneas_entry.ml_kem_512.encapsulate_deterministic
  | .k768 => aeneas_entry.ml_kem_768.encapsulate_deterministic
  | .k1024 => aeneas_entry.ml_kem_1024.encapsulate_deterministic

/-- `DecapsulationKey::decapsulate` at each size. -/
def decapsulate : (s : Size) → s.DK → Array U8 s.ctLen → Result (Array U8 32#usize)
  | .k512 => aeneas_entry.ml_kem_512.decapsulate
  | .k768 => aeneas_entry.ml_kem_768.decapsulate
  | .k1024 => aeneas_entry.ml_kem_1024.decapsulate

-- The spec's sizes are the Rust ones
theorem ekSize (s : Size) : Wychelean.KEM.MLKEM.ekLen s.ps = s.ekLen.val := by cases s <;> rfl
theorem ctSize (s : Size) : Wychelean.KEM.MLKEM.ctLen s.ps = s.ctLen.val := by cases s <;> rfl

end Size

/-- Rejection sampling (FIPS 203, Algorithm 7) halts on every input. The theorems that run it (all
but `ek_from_bytes_then_to_bytes`) assume this; see `MlKem.Properties.SampleNTTHalts`. -/
abbrev SampleNTTHalts : Prop := MlKem.Properties.SampleNTTHalts

/-- keygen → encapsulation key → to_bytes matches the spec -/
theorem keygen_then_to_bytes (h : SampleNTTHalts) : ∀ (s : Size) (seed : Array U8 64#usize),
    (do let dk ← s.fromSeed seed
        let ek ← s.encapsulationKey dk
        s.ekToBytes ek)
      ⦃ (r : Array U8 s.ekLen) =>
          (arrayToBytes r).toList = (KeyGen s.ps (seedD seed) (seedZ seed)).1.toList ⦄
  | .k512, seed => MlKem.Properties.keygen_to_bytes_512 h seed
  | .k768, seed => MlKem.Properties.keygen_to_bytes_768 h seed
  | .k1024, seed => MlKem.Properties.keygen_to_bytes_1024 h seed

/-- keygen → encapsulation key → encapsulate matches the spec -/
theorem keygen_then_encapsulate (h : SampleNTTHalts) : ∀ (s : Size) (seed : Array U8 64#usize) (m : Array U8 32#usize),
    (do let dk ← s.fromSeed seed
        let ek ← s.encapsulationKey dk
        s.encapsulate ek m)
      ⦃ (ct : Array U8 s.ctLen) (ss : Array U8 32#usize) =>
          Encaps s.ps (KeyGen s.ps (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast s.ctSize.symm) ⦄
  | .k512, seed, m => MlKem.Properties.keygen_encap_512 h seed m
  | .k768, seed, m => MlKem.Properties.keygen_encap_768 h seed m
  | .k1024, seed, m => MlKem.Properties.keygen_encap_1024 h seed m

/-- from_bytes → encapsulate matches the spec. Unlike the others, deserialization can fail: the
spec's `Encaps` checks its input key, and the Rust impl does the same check when deserializing it.
The theorem says that these checks agree, and that when they pass, the outputs agree. -/
theorem from_bytes_then_encapsulate (h : SampleNTTHalts) : ∀ (s : Size) (ek_bytes : Array U8 s.ekLen)
    (m : Array U8 32#usize),
    (MlKem.Properties.whenOk (s.ekFromBytes ek_bytes) fun ek => s.encapsulate ek m)
      ⦃ (r : Option (Array U8 s.ctLen × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast s.ctSize.symm))
            = Encaps s.ps ((arrayToBytes ek_bytes).cast s.ekSize.symm) (arrayToBytes m) ⦄
  | .k512, ek, m => MlKem.Properties.from_bytes_encap_512 h ek m
  | .k768, ek, m => MlKem.Properties.from_bytes_encap_768 h ek m
  | .k1024, ek, m => MlKem.Properties.from_bytes_encap_1024 h ek m

/-- ek from_bytes → to_bytes is the identity on bytes, whenever from_bytes succeeds. Note this doesn't
make any reference to the spec, since the spec only ever represents keys as byte strings. Instead, we
check that the Rust impl's notion of an encapsulation key is consistent with itself. -/
theorem ek_from_bytes_then_to_bytes : ∀ (s : Size) (ek_bytes : Array U8 s.ekLen),
    (MlKem.Properties.whenOk (s.ekFromBytes ek_bytes) fun ek => s.ekToBytes ek)
      ⦃ (r : Option (Array U8 s.ekLen)) => ∀ b, r = some b → b = ek_bytes ⦄
  | .k512, ek => MlKem.Properties.from_bytes_to_bytes_512 ek
  | .k768, ek => MlKem.Properties.from_bytes_to_bytes_768 ek
  | .k1024, ek => MlKem.Properties.from_bytes_to_bytes_1024 ek

/-- dk from_seed → to_seed is the identity on bytes. Similar to above, this doesn't make any reference
to the spec, which only ever represents the seed as bytes. -/
theorem from_seed_then_to_seed (h : SampleNTTHalts) : ∀ (s : Size) (seed : Array U8 64#usize),
    (do let dk ← s.fromSeed seed
        s.toSeed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄
  | .k512, seed => MlKem.Properties.from_seed_to_seed_512 h seed
  | .k768, seed => MlKem.Properties.from_seed_to_seed_768 h seed
  | .k1024, seed => MlKem.Properties.from_seed_to_seed_1024 h seed

/-- keygen → decapsulate matches the spec -/
theorem keygen_then_decapsulate (h : SampleNTTHalts) : ∀ (s : Size) (seed : Array U8 64#usize) (ct : Array U8 s.ctLen),
    (do let dk ← s.fromSeed seed
        s.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps s.ps (KeyGen s.ps (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast s.ctSize.symm)
            = some (arrayToBytes r) ⦄
  | .k512, seed, ct => MlKem.Properties.keygen_decap_512 h seed ct
  | .k768, seed, ct => MlKem.Properties.keygen_decap_768 h seed ct
  | .k1024, seed, ct => MlKem.Properties.keygen_decap_1024 h seed ct

end MlKem.TopLevel
