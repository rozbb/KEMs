import MlKem.Properties.Kem

/-! The per-parameter-set statements of the theorems in `TopLevelTheorems.lean`. -/

open Aeneas Aeneas.Std Result
open Wychelean (pack unpack)
open Wychelean.KEM.MLKEM (ParameterSet KeyGen Encaps Decaps)
open Wychelean.KEM.MLKEM
open MlKem.Properties.Kem
open RustMlKem

namespace MlKem.Properties

set_option maxRecDepth 20000

theorem spec_some_map {α : Type} {x : Result α} {P : Option α → Prop} (h : x ⦃ r => P (some r) ⦄) :
    (some <$> x) ⦃ P ⦄ := by
  rw [← bind_pure_comp]
  exact WP.spec_bind h (fun r hr => by simpa [pure, WP.spec_ok] using hr)

section ML_KEM_512

theorem keygen_to_bytes_512 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        let ek ← aeneas_entry.ml_kem_512.encapsulation_key dk
        aeneas_entry.ml_kem_512.ek_to_bytes ek)
      ⦃ (r : Array U8 800#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  simp only [aeneas_entry.ml_kem_512.from_seed, aeneas_entry.ml_kem_512.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem512.encapsulation_key_MlKem512MlKem512, aeneas_entry.ml_kem_512.ek_to_bytes]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  exact congrArg Vector.toList r_post

theorem keygen_encap_512 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        let ek ← aeneas_entry.ml_kem_512.encapsulation_key dk
        aeneas_entry.ml_kem_512.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 768#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_512 (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  simp only [aeneas_entry.ml_kem_512.from_seed, aeneas_entry.ml_kem_512.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem512.encapsulation_key_MlKem512MlKem512, aeneas_entry.ml_kem_512.encapsulate_deterministic]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [Encaps_of_KeyCheck _ _ _ (KeyCheck_pack _ _), ct_post]
  rfl

theorem from_bytes_encap_512 (hT : SampleNTTHalts) (ek_bytes : Array U8 800#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_512.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_512.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 768#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_512 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_512.ek_from_bytes, aeneas_entry.ml_kem_512.encapsulate_deterministic]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    refine Eq.trans ?_ (Encaps_of_KeyCheck _ _ _ hkc).symm
    rw [hek] at r_post
    simp only [Option.map_some]
    exact congrArg some (Internal.Encaps_of_KeyCheck _ _ hkc _ _ r_post).symm
  · rename_i h
    subst h
    exact (Encaps_of_not_KeyCheck _ _ _ x_post).symm

theorem from_bytes_to_bytes_512 (ek_bytes : Array U8 800#usize) :
    (whenOk (aeneas_entry.ml_kem_512.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_512.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 800#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_512.ek_from_bytes, aeneas_entry.ml_kem_512.ek_to_bytes]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    cases r_post1
    apply (Pke.arrayToBytes_inj _ _).mp
    rw [r_post, hek]
    exact pack_unpack_of_KeyCheck _ _ hkc

theorem from_seed_to_seed_512 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        aeneas_entry.ml_kem_512.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  simp only [aeneas_entry.ml_kem_512.from_seed, aeneas_entry.ml_kem_512.to_seed,
    decapsulation_key.DecapsulationKey_MlKem512.to_seed_MlKem512MlKem512,
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32]
  step*
  rename_i h
  rw [dk_post3] at h
  cases h
  rw [auu2_post, dk_post4]
  exact congrArg some (concat_split seed _)

theorem keygen_decap_512 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (ct : Array U8 768#usize) :
    (do let dk ← aeneas_entry.ml_kem_512.from_seed seed
        aeneas_entry.ml_kem_512.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_512 (KeyGen .ML_KEM_512 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  simp only [aeneas_entry.ml_kem_512.from_seed, aeneas_entry.ml_kem_512.decapsulate]
  step*
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [← dk_post2, Decaps_pack]
  exact congrArg some r_post

end ML_KEM_512

section ML_KEM_768

theorem keygen_to_bytes_768 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        let ek ← aeneas_entry.ml_kem_768.encapsulation_key dk
        aeneas_entry.ml_kem_768.ek_to_bytes ek)
      ⦃ (r : Array U8 1184#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  simp only [aeneas_entry.ml_kem_768.from_seed, aeneas_entry.ml_kem_768.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem768.encapsulation_key_MlKem768MlKem768, aeneas_entry.ml_kem_768.ek_to_bytes]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  exact congrArg Vector.toList r_post

theorem keygen_encap_768 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        let ek ← aeneas_entry.ml_kem_768.encapsulation_key dk
        aeneas_entry.ml_kem_768.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 1088#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_768 (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  simp only [aeneas_entry.ml_kem_768.from_seed, aeneas_entry.ml_kem_768.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem768.encapsulation_key_MlKem768MlKem768, aeneas_entry.ml_kem_768.encapsulate_deterministic]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [Encaps_of_KeyCheck _ _ _ (KeyCheck_pack _ _), ct_post]
  rfl

theorem from_bytes_encap_768 (hT : SampleNTTHalts) (ek_bytes : Array U8 1184#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_768.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_768.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 1088#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_768 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_768.ek_from_bytes, aeneas_entry.ml_kem_768.encapsulate_deterministic]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    refine Eq.trans ?_ (Encaps_of_KeyCheck _ _ _ hkc).symm
    rw [hek] at r_post
    simp only [Option.map_some]
    exact congrArg some (Internal.Encaps_of_KeyCheck _ _ hkc _ _ r_post).symm
  · rename_i h
    subst h
    exact (Encaps_of_not_KeyCheck _ _ _ x_post).symm

theorem from_bytes_to_bytes_768 (ek_bytes : Array U8 1184#usize) :
    (whenOk (aeneas_entry.ml_kem_768.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_768.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 1184#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_768.ek_from_bytes, aeneas_entry.ml_kem_768.ek_to_bytes]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    cases r_post1
    apply (Pke.arrayToBytes_inj _ _).mp
    rw [r_post, hek]
    exact pack_unpack_of_KeyCheck _ _ hkc

theorem from_seed_to_seed_768 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        aeneas_entry.ml_kem_768.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  simp only [aeneas_entry.ml_kem_768.from_seed, aeneas_entry.ml_kem_768.to_seed,
    decapsulation_key.DecapsulationKey_MlKem768.to_seed_MlKem768MlKem768,
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32]
  step*
  rename_i h
  rw [dk_post3] at h
  cases h
  rw [auu2_post, dk_post4]
  exact congrArg some (concat_split seed _)

theorem keygen_decap_768 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (ct : Array U8 1088#usize) :
    (do let dk ← aeneas_entry.ml_kem_768.from_seed seed
        aeneas_entry.ml_kem_768.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_768 (KeyGen .ML_KEM_768 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  simp only [aeneas_entry.ml_kem_768.from_seed, aeneas_entry.ml_kem_768.decapsulate]
  step*
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [← dk_post2, Decaps_pack]
  exact congrArg some r_post

end ML_KEM_768

section ML_KEM_1024

theorem keygen_to_bytes_1024 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        let ek ← aeneas_entry.ml_kem_1024.encapsulation_key dk
        aeneas_entry.ml_kem_1024.ek_to_bytes ek)
      ⦃ (r : Array U8 1568#usize) =>
          (arrayToBytes r).toList = (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).1.toList ⦄ := by
  simp only [aeneas_entry.ml_kem_1024.from_seed, aeneas_entry.ml_kem_1024.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem1024.encapsulation_key_MlKem1024MlKem1024, aeneas_entry.ml_kem_1024.ek_to_bytes]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  exact congrArg Vector.toList r_post

theorem keygen_encap_1024 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (m : Array U8 32#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        let ek ← aeneas_entry.ml_kem_1024.encapsulation_key dk
        aeneas_entry.ml_kem_1024.encapsulate_deterministic ek m)
      ⦃ (ct : Array U8 1568#usize) (ss : Array U8 32#usize) =>
          Encaps .ML_KEM_1024 (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).1 (arrayToBytes m)
            = some (arrayToBytes ss, (arrayToBytes ct).cast rfl) ⦄ := by
  simp only [aeneas_entry.ml_kem_1024.from_seed, aeneas_entry.ml_kem_1024.encapsulation_key,
    decapsulation_key.DecapsulationKey_MlKem1024.encapsulation_key_MlKem1024MlKem1024, aeneas_entry.ml_kem_1024.encapsulate_deterministic]
  step*
  all_goals try exact dk_post.1
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [Encaps_of_KeyCheck _ _ _ (KeyCheck_pack _ _), ct_post]
  rfl

theorem from_bytes_encap_1024 (hT : SampleNTTHalts) (ek_bytes : Array U8 1568#usize) (m : Array U8 32#usize) :
    (whenOk (aeneas_entry.ml_kem_1024.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_1024.encapsulate_deterministic ek m)
      ⦃ (r : Option (Array U8 1568#usize × Array U8 32#usize)) =>
          r.map (fun (ct, ss) => (arrayToBytes ss, (arrayToBytes ct).cast rfl))
            = Encaps .ML_KEM_1024 ((arrayToBytes ek_bytes).cast rfl) (arrayToBytes m) ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_1024.ek_from_bytes, aeneas_entry.ml_kem_1024.encapsulate_deterministic]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    refine Eq.trans ?_ (Encaps_of_KeyCheck _ _ _ hkc).symm
    rw [hek] at r_post
    simp only [Option.map_some]
    exact congrArg some (Internal.Encaps_of_KeyCheck _ _ hkc _ _ r_post).symm
  · rename_i h
    subst h
    exact (Encaps_of_not_KeyCheck _ _ _ x_post).symm

theorem from_bytes_to_bytes_1024 (ek_bytes : Array U8 1568#usize) :
    (whenOk (aeneas_entry.ml_kem_1024.ek_from_bytes ek_bytes) fun ek => aeneas_entry.ml_kem_1024.ek_to_bytes ek)
      ⦃ (r : Option (Array U8 1568#usize)) => ∀ b, r = some b → b = ek_bytes ⦄ := by
  simp only [whenOk, aeneas_entry.ml_kem_1024.ek_from_bytes, aeneas_entry.ml_kem_1024.ek_to_bytes]
  step*
  · rename_i h
    subst h
    obtain ⟨hinv, hek, hkc⟩ := x_post
    apply spec_some_map
    step*
    cases r_post1
    apply (Pke.arrayToBytes_inj _ _).mp
    rw [r_post, hek]
    exact pack_unpack_of_KeyCheck _ _ hkc

theorem from_seed_to_seed_1024 (hT : SampleNTTHalts) (seed : Array U8 64#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        aeneas_entry.ml_kem_1024.to_seed dk)
      ⦃ (r : Option (Array U8 64#usize)) => r = some seed ⦄ := by
  simp only [aeneas_entry.ml_kem_1024.from_seed, aeneas_entry.ml_kem_1024.to_seed,
    decapsulation_key.DecapsulationKey_MlKem1024.to_seed_MlKem1024MlKem1024,
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32]
  step*
  rename_i h
  rw [dk_post3] at h
  cases h
  rw [auu2_post, dk_post4]
  exact congrArg some (concat_split seed _)

theorem keygen_decap_1024 (hT : SampleNTTHalts) (seed : Array U8 64#usize) (ct : Array U8 1568#usize) :
    (do let dk ← aeneas_entry.ml_kem_1024.from_seed seed
        aeneas_entry.ml_kem_1024.decapsulate dk ct)
      ⦃ (r : Array U8 32#usize) =>
          Decaps .ML_KEM_1024 (KeyGen .ML_KEM_1024 (seedD seed) (seedZ seed)).2 ((arrayToBytes ct).cast rfl)
            = some (arrayToBytes r) ⦄ := by
  simp only [aeneas_entry.ml_kem_1024.from_seed, aeneas_entry.ml_kem_1024.decapsulate]
  step*
  rw [KeyGen_of _ _ _ _ _ dk_post1]
  dsimp only
  rw [← dk_post2, Decaps_pack]
  exact congrArg some r_post

end ML_KEM_1024

end MlKem.Properties
