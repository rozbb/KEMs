import MlKem.Properties.Basic

/-! The per-parameter-set statements of the theorems in `TopLevelTheorems.lean`. -/

open Aeneas Aeneas.Std Result
open Wychelean.KEM.MLKEM (ParameterSet KeyGen Encaps Decaps)
open RustMlKem

namespace MlKem.Properties

section ML_KEM_512

theorem keygen_to_bytes_512 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        let ek ← aeneas_entry.ml_kem_512.encapsulation_key dk
        aeneas_entry.ml_kem_512.ek_to_bytes ek)
      ⦃ (r : Array U8 800#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  sorry

theorem keygen_encap_512 (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        let ek ← aeneas_entry.ml_kem_512.encapsulation_key dk
        aeneas_entry.ml_kem_512.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 768#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_512 (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  sorry

theorem from_bytes_encap_512 (ek_bytes : Array U8 800#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_512.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_512.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 768#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_512 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  sorry

theorem from_bytes_to_bytes_512 (ek_bytes : Array U8 800#usize) :
    (whenOk (aeneas_entry.ml_kem_512.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_512.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 800#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  sorry

theorem from_seed_to_seed_512 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        aeneas_entry.ml_kem_512.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  sorry

theorem keygen_decap_512 (seed : Array U8 64#usize) (ct : Array U8 768#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        aeneas_entry.ml_kem_512.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_512 (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  sorry

end ML_KEM_512

section ML_KEM_768

theorem keygen_to_bytes_768 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        let ek ← aeneas_entry.ml_kem_768.encapsulation_key dk
        aeneas_entry.ml_kem_768.ek_to_bytes ek)
      ⦃ (r : Array U8 1184#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  sorry

theorem keygen_encap_768 (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        let ek ← aeneas_entry.ml_kem_768.encapsulation_key dk
        aeneas_entry.ml_kem_768.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 1088#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_768 (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  sorry

theorem from_bytes_encap_768 (ek_bytes : Array U8 1184#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_768.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_768.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 1088#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_768 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  sorry

theorem from_bytes_to_bytes_768 (ek_bytes : Array U8 1184#usize) :
    (whenOk (aeneas_entry.ml_kem_768.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_768.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 1184#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  sorry

theorem from_seed_to_seed_768 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        aeneas_entry.ml_kem_768.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  sorry

theorem keygen_decap_768 (seed : Array U8 64#usize) (ct : Array U8 1088#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        aeneas_entry.ml_kem_768.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_768 (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  sorry

end ML_KEM_768

section ML_KEM_1024

theorem keygen_to_bytes_1024 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        let ek ← aeneas_entry.ml_kem_1024.encapsulation_key dk
        aeneas_entry.ml_kem_1024.ek_to_bytes ek)
      ⦃ (r : Array U8 1568#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  sorry

theorem keygen_encap_1024 (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        let ek ← aeneas_entry.ml_kem_1024.encapsulation_key dk
        aeneas_entry.ml_kem_1024.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 1568#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_1024 (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  sorry

theorem from_bytes_encap_1024 (ek_bytes : Array U8 1568#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_1024.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_1024.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 1568#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_1024 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  sorry

theorem from_bytes_to_bytes_1024 (ek_bytes : Array U8 1568#usize) :
    (whenOk (aeneas_entry.ml_kem_1024.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_1024.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 1568#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  sorry

theorem from_seed_to_seed_1024 (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        aeneas_entry.ml_kem_1024.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  sorry

theorem keygen_decap_1024 (seed : Array U8 64#usize) (ct : Array U8 1568#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        aeneas_entry.ml_kem_1024.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_1024 (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  sorry

end ML_KEM_1024

end MlKem.Properties
