import MlKem.Properties.Pke

/-! # ML-KEM

The Rust ML-KEM (`DecapsulationKey`, `EncapsulationKey`) matches the spec's ML-KEM (§6, §7):
deterministic key generation from a seed, encapsulation, decapsulation, and (de)serialization of the
encapsulation key. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec pack unpack)
open Wychelean.Hashes
open Wychelean.KEM.MLKEM
open RustMlKem
open scoped Wychelean.Notations Wychelean.Utils.Linear

namespace MlKem.Properties

set_option maxRecDepth 20000

/-! ## Facts about the spec -/

namespace Kem

theorem KeyGen_of (p : ParameterSet) (d z : Seed) (e : EkPKE p) (dd : DkPKE p)
    (h : K_PKE.KeyGen p d = (e, dd)) :
    KeyGen p d z = (pack e, pack (⟨dd, pack e, H (pack e), z⟩ : Dk p)) := by
  simp only [KeyGen, Internal.KeyGen, h]

theorem KeyCheck_pack (p : ParameterSet) (e : EkPKE p) : Encaps.KeyCheck p (pack e) = true := by
  simp [Encaps.KeyCheck, unpack_pack_ekPKE]

theorem Encaps_of_KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed)
    (h : Encaps.KeyCheck p ek = true) : Encaps p ek m = some (Internal.Encaps p ek m) := by
  simp [Encaps, h]

theorem Encaps_of_not_KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed)
    (h : Encaps.KeyCheck p ek = false) : Encaps p ek m = none := by
  simp [Encaps, h]

theorem pack_unpack_of_KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p))
    (h : Encaps.KeyCheck p ek = true) : pack (unpack ek : EkPKE p) = ek := by
  simpa [Encaps.KeyCheck] using h

theorem Internal.Encaps_of_KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p))
    (h : Encaps.KeyCheck p ek = true) (m : Seed) (x : SharedKey × ByteVec (ctLen p))
    (hx : Internal.Encaps p (pack (unpack ek : EkPKE p)) m = x) : Internal.Encaps p ek m = x := by
  rwa [pack_unpack_of_KeyCheck p ek h] at hx

theorem Internal.Encaps_eq (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) (e : EkPKE p)
    (he : unpack ek = e) (K r : Seed) (hG : G (m ‖ H ek) = (K, r)) :
    Internal.Encaps p ek m = (K, pack (K_PKE.Encrypt p e m r)) := by
  simp only [Internal.Encaps, hG, he]

theorem Decaps_pack (p : ParameterSet) (dd : DkPKE p) (ek : ByteVec (ekLen p)) (z : Seed)
    (c : ByteVec (ctLen p)) :
    Decaps p (pack (⟨dd, ek, H ek, z⟩ : Dk p)) c =
      some (Internal.Decaps p (pack (⟨dd, ek, H ek, z⟩ : Dk p)) c) := by
  simp [Decaps, Decaps.KeyCheck, unpack_pack_dk]

theorem Internal.Decaps_eq (p : ParameterSet) (dd : DkPKE p) (ek : ByteVec (ekLen p)) (z : Seed)
    (c : ByteVec (ctLen p)) (e : EkPKE p) (he : unpack ek = e) (m' : Seed)
    (hm : K_PKE.Decrypt p dd (unpack c) = m') (K' r' : Seed) (hG : G (m' ‖ H ek) = (K', r'))
    (Kbar : Seed) (hJ : J (z ‖ c) = Kbar) :
    Internal.Decaps p (pack (⟨dd, ek, H ek, z⟩ : Dk p)) c =
      if c ≠ pack (K_PKE.Encrypt p e m' r') then Kbar else K' := by
  simp only [Internal.Decaps, unpack_pack_dk, hm, hG, hJ, he]

/-! ## Glue -/

/-- Concatenating two Rust arrays, as the spec does. -/
theorem bytesOfList_append_arrays {n m : Usize} (a : Std.Array U8 n) (b : Std.Array U8 m) :
    (bytesOfList (a.val ++ b.val)).toList = (arrayToBytes a ‖ arrayToBytes b).toList := by
  simp only [toList_bytesOfList, toList_vector_append, toList_arrayToBytes, List.map_append]

theorem G_arrays (a b : Std.Array U8 32#usize) :
    G (bytesOfList (a.val ++ b.val)) = G (arrayToBytes a ‖ arrayToBytes b) :=
  byteVec_fun_congr (fun _ v => G v) (bytesOfList_append_arrays a b)

theorem split_fst_64 (v : ByteVec 64) :
    (Wychelean.split v 32 32).1 = Vector.ofFn fun i : Fin 32 => v[i.val] := by
  apply Vector.ext; intro i hi
  simp [Wychelean.split, Wychelean.slice]

theorem split_snd_64 (v : ByteVec 64) :
    (Wychelean.split v 32 32).2 = Vector.ofFn fun i : Fin 32 => v[32 + i.val] := by
  apply Vector.ext; intro i hi
  simp [Wychelean.split, Wychelean.slice]

theorem J_arrays {n m : Usize} (a : Std.Array U8 n) (b : Std.Array U8 m) :
    J (bytesOfList (a.val ++ b.val)) = J (arrayToBytes a ‖ arrayToBytes b) :=
  byteVec_fun_congr (fun _ v => J v) (bytesOfList_append_arrays a b)

/-- The constant-time selection at the end of decapsulation. -/
theorem select_eq {n : Usize} (ct cp : Std.Array U8 n) (x : ByteVec n) (hx : arrayToBytes cp = x)
    (A B : Std.Array U8 32#usize) :
    (if arrayToBytes ct ≠ x then arrayToBytes A else arrayToBytes B) =
      arrayToBytes (if decide ((Array.to_slice cp).val = (Array.to_slice ct).val) then B else A) := by
  subst hx
  by_cases hc : cp = ct
  · subst hc; simp
  · have : arrayToBytes ct ≠ arrayToBytes cp := fun h => hc ((Pke.arrayToBytes_inj _ _).mp h).symm
    have h2 : cp.val ≠ ct.val := fun h => hc (Aeneas.Std.Array.ext _ _ h)
    simp [this, h2]

theorem seedD_split (seed : Std.Array U8 64#usize) :
    arrayToBytes (Model.split (n := 32#usize) (m := 32#usize) seed).1 = seedD seed :=
  (congrArg Prod.fst (Pke.arrayToBytes_split seed rfl)).trans (split_fst_64 (arrayToBytes seed))

theorem seedZ_split (seed : Std.Array U8 64#usize) :
    arrayToBytes (Model.split (n := 32#usize) (m := 32#usize) seed).2 = seedZ seed :=
  (congrArg Prod.snd (Pke.arrayToBytes_split seed rfl)).trans (split_snd_64 (arrayToBytes seed))

theorem concat_split {n m k : Usize} (a : Std.Array U8 k) (h : n.val + m.val = k.val) :
    Model.concat (Model.split (n := n) (m := m) a h).1 (Model.split (n := n) (m := m) a h).2 h = a := by
  apply Aeneas.Std.Array.ext
  simp [Model.concat, Model.split, Array.from_val]

@[step] theorem split_64 (a : Std.Array U8 64#usize) :
    hybrid_array.Array_u8_U64.split_u8_U64_U32U8U64U32 a
      ⦃ (x y : Std.Array U8 32#usize) => (x, y) = Model.split a ⦄ := by
  simp [hybrid_array.Array_u8_U64.split_u8_U64_U32U8U64U32, WP.uncurry'_eq]

@[step] theorem concat_32 (a b : Std.Array U8 32#usize) :
    hybrid_array.Array_u8_U32.concat_u8_U32_U32U8U32U32 a b ⦃ c => c = Model.concat a b ⦄ := by
  simp [hybrid_array.Array_u8_U32.concat_u8_U32_U32U8U32U32]

@[step] theorem deref_32 (a : Std.Array U8 32#usize) :
    hybrid_array.Array_u8_U32_Deref.deref_u8_U32U8U32 a ⦃ s => s.val = a.val ⦄ := by
  simp [hybrid_array.Array_u8_U32_Deref.deref_u8_U32U8U32]

@[step] theorem as_slice_32 (a : Std.Array U8 32#usize) :
    hybrid_array.Array_u8_U32.as_slice_u8_U32U8U32 a ⦃ s => s.val = a.val ⦄ := by
  simp [hybrid_array.Array_u8_U32.as_slice_u8_U32U8U32]

@[step] theorem ct_eq_slices (a b : Slice U8) :
    ctutils.traits.ct_eq.Sliceu8_CtEq_Sliceu8.ct_eq_u8U8 a b ⦃ c => c = decide (a.val = b.val) ⦄ := by
  simp [ctutils.traits.ct_eq.Sliceu8_CtEq_Sliceu8.ct_eq_u8U8]

@[step] theorem ct_select_32 (a b : Std.Array U8 32#usize) (c : Bool) :
    hybrid_array.Array_u8_U32_CtSelect.ct_select_u8_U32U8U32 a b c ⦃ r => r = if c then b else a ⦄ := by
  simp [hybrid_array.Array_u8_U32_CtSelect.ct_select_u8_U32U8U32]

end Kem

open Kem

/-! ## ML-KEM-512 -/

/-- What the Rust code maintains about an encapsulation key: its polynomials are reduced and `h` is
the hash of its encoding. -/
def ekInv512 (ek : encapsulation_key.EncapsulationKey_MlKem512) : Prop :=
  Vec.Bounded q ek.ek_pke.inner.t_hat ∧ arrayToBytes ek.h = H (pack (ekPKE512 ek.ek_pke.inner))

@[step] theorem from_encryption_key_spec_512 (e : pke.EncryptionKey_MlKem512) (he : Vec.Bounded q e.t_hat) :
    encapsulation_key.EncapsulationKey_MlKem512.from_encryption_key_MlKem512MlKem512 e
      ⦃ ek => ek.ek_pke.inner = e ∧ ekInv512 ek ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem512.from_encryption_key_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem512.new_EncryptionKey_MlKem512EncryptionKey_MlKem512
  step*
  refine ⟨he, h_post.trans ?_⟩
  exact byteVec_fun_congr (fun _ v => H v) (congrArg Vector.toList auu_post)

/-- What the Rust code maintains about a decapsulation key. -/
def dkInv512 (dk : decapsulation_key.DecapsulationKey_MlKem512) : Prop :=
  ekInv512 dk.ek ∧ Vec.Bounded q dk.dk_pke.inner.s_hat

/-- A Rust decapsulation key as the spec's (expanded) one. -/
def dk512 (dk : decapsulation_key.DecapsulationKey_MlKem512) : Dk .ML_KEM_512 :=
  ⟨dkPKE512 dk.dk_pke.inner, pack (ekPKE512 dk.ek.ek_pke.inner), H (pack (ekPKE512 dk.ek.ek_pke.inner)),
    arrayToBytes dk.z.inner⟩

@[step] theorem from_seed_spec_512 (seed : Std.Array U8 64#usize) :
    decapsulation_key.DecapsulationKey_MlKem512.from_seed_MlKem512MlKem512 seed
      ⦃ dk => dkInv512 dk ∧
          K_PKE.KeyGen .ML_KEM_512 (seedD seed) = (ekPKE512 dk.ek.ek_pke.inner, dkPKE512 dk.dk_pke.inner) ∧
          arrayToBytes dk.z.inner = seedZ seed ∧
          dk.d = some ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).1⟩ ∧
          dk.z = ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).2⟩ ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem512.from_seed_MlKem512MlKem512
    decapsulation_key.DecapsulationKey_MlKem512.generate_deterministic_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem512.new_DecryptionKey_MlKem512DecryptionKey_MlKem512
    module_lattice.maybe_box.MaybeBox_Array_u8_U32.new_Array_u8_U32Array_u8_U32
  step*
  have hd : d = (Model.split (n := 32#usize) (m := 32#usize) seed).1 := by rw [← d_post]
  have hz : z = (Model.split (n := 32#usize) (m := 32#usize) seed).2 := by rw [← d_post]
  refine ⟨⟨ek_post, dk_pke_post⟩, ?_, ?_, by rw [hd], by rw [hz]⟩
  · rw [ek_pke_post, ← dk_pke_post2, hd, seedD_split]
  · rw [hz, seedZ_split]

@[step] theorem ek_export_spec_512 (ek : encapsulation_key.EncapsulationKey_MlKem512) (h : ekInv512 ek) :
    encapsulation_key.EncapsulationKey_MlKem512_KeyExport.to_bytes_MlKem512MlKem512 ek
      ⦃ b => arrayToBytes b = pack (ekPKE512 ek.ek_pke.inner) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem512_KeyExport.to_bytes_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem512_Deref.deref_EncryptionKey_MlKem512EncryptionKey_MlKem512
  have := h.1
  step*

@[step] theorem encapsulate_spec_512 (ek : encapsulation_key.EncapsulationKey_MlKem512) (h : ekInv512 ek)
    (m : Std.Array U8 32#usize) :
    encapsulation_key.EncapsulationKey_MlKem512.encapsulate_deterministic_MlKem512MlKem512 ek m
      ⦃ (c : Std.Array U8 768#usize) (K : Std.Array U8 32#usize) =>
          Internal.Encaps .ML_KEM_512 (pack (ekPKE512 ek.ek_pke.inner)) (arrayToBytes m) =
            (arrayToBytes K, arrayToBytes c) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem512.encapsulate_deterministic_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem512_Deref.deref_EncryptionKey_MlKem512EncryptionKey_MlKem512
  have := h.1
  step*
  have hG : G (arrayToBytes m ‖ H (pack (ekPKE512 ek.ek_pke.inner))) = (arrayToBytes K, arrayToBytes r) := by
    rw [← h.2]
    refine (G_arrays m ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact K_post.symm
  refine (Internal.Encaps_eq _ _ _ _ (unpack_pack_ekPKE _ _) _ _ hG).trans ?_
  rw [c_post]
  rfl

@[step] theorem decapsulate_spec_512 (dk : decapsulation_key.DecapsulationKey_MlKem512) (h : dkInv512 dk)
    (ct : Std.Array U8 768#usize) :
    decapsulation_key.DecapsulationKey_MlKem512_Decapsulate.decapsulate_MlKem512MlKem512 dk ct
      ⦃ K => Internal.Decaps .ML_KEM_512 (pack (dk512 dk)) (arrayToBytes ct) = arrayToBytes K ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem512_Decapsulate.decapsulate_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem512_Deref.deref_DecryptionKey_MlKem512DecryptionKey_MlKem512
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32
    encapsulation_key.EncapsulationKey_MlKem512.h_MlKem512MlKem512
    encapsulation_key.EncapsulationKey_MlKem512.ek_pke_MlKem512MlKem512
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem512_Deref.deref_EncryptionKey_MlKem512EncryptionKey_MlKem512
    hybrid_array.Array_u8_U768_AsRef_Sliceu8.as_ref_u8_U768U8U768
    hybrid_array.Array_u8_U768_Deref.deref_u8_U768U8U768
  have := h.1.1
  have := h.2
  step*
  have hG : G (arrayToBytes mp ‖ H (pack (ekPKE512 dk.ek.ek_pke.inner))) = (arrayToBytes Kp, arrayToBytes rp) := by
    rw [← h.1.2]
    refine (G_arrays mp dk.ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact Kp_post.symm
  have hJ : J (arrayToBytes dk.z.inner ‖ arrayToBytes ct) = arrayToBytes Kbar := by
    refine (J_arrays dk.z.inner ct).symm.trans ?_
    rw [← s2_post, Kbar_post, Array.val_to_slice]
  unfold dk512
  refine (Internal.Decaps_eq .ML_KEM_512 (dkPKE512 dk.dk_pke.inner) (pack (ekPKE512 dk.ek.ek_pke.inner))
    (arrayToBytes dk.z.inner) (arrayToBytes ct) _ (unpack_pack_ekPKE _ _) _ mp_post.symm _ _ hG _ hJ).trans ?_
  rw [K_post, c_post]
  exact select_eq (n := 768#usize) ct cp _ cp_post Kbar Kp

@[step] theorem ek_new_spec_512 (b : Std.Array U8 800#usize) :
    encapsulation_key.EncapsulationKey_MlKem512.new_MlKem512MlKem512 b
      ⦃ r => match r with
        | .Ok ek => ekInv512 ek ∧ ekPKE512 ek.ek_pke.inner = unpack (arrayToBytes b) ∧
            Encaps.KeyCheck .ML_KEM_512 (arrayToBytes b)
        | .Err _ => Encaps.KeyCheck .ML_KEM_512 (arrayToBytes b) = false ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem512.new_MlKem512MlKem512
  step*

/-! ## ML-KEM-768 -/

/-- What the Rust code maintains about an encapsulation key: its polynomials are reduced and `h` is
the hash of its encoding. -/
def ekInv768 (ek : encapsulation_key.EncapsulationKey_MlKem768) : Prop :=
  Vec.Bounded q ek.ek_pke.inner.t_hat ∧ arrayToBytes ek.h = H (pack (ekPKE768 ek.ek_pke.inner))

@[step] theorem from_encryption_key_spec_768 (e : pke.EncryptionKey_MlKem768) (he : Vec.Bounded q e.t_hat) :
    encapsulation_key.EncapsulationKey_MlKem768.from_encryption_key_MlKem768MlKem768 e
      ⦃ ek => ek.ek_pke.inner = e ∧ ekInv768 ek ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem768.from_encryption_key_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem768.new_EncryptionKey_MlKem768EncryptionKey_MlKem768
  step*
  refine ⟨he, h_post.trans ?_⟩
  exact byteVec_fun_congr (fun _ v => H v) (congrArg Vector.toList auu_post)

/-- What the Rust code maintains about a decapsulation key. -/
def dkInv768 (dk : decapsulation_key.DecapsulationKey_MlKem768) : Prop :=
  ekInv768 dk.ek ∧ Vec.Bounded q dk.dk_pke.inner.s_hat

/-- A Rust decapsulation key as the spec's (expanded) one. -/
def dk768 (dk : decapsulation_key.DecapsulationKey_MlKem768) : Dk .ML_KEM_768 :=
  ⟨dkPKE768 dk.dk_pke.inner, pack (ekPKE768 dk.ek.ek_pke.inner), H (pack (ekPKE768 dk.ek.ek_pke.inner)),
    arrayToBytes dk.z.inner⟩

@[step] theorem from_seed_spec_768 (seed : Std.Array U8 64#usize) :
    decapsulation_key.DecapsulationKey_MlKem768.from_seed_MlKem768MlKem768 seed
      ⦃ dk => dkInv768 dk ∧
          K_PKE.KeyGen .ML_KEM_768 (seedD seed) = (ekPKE768 dk.ek.ek_pke.inner, dkPKE768 dk.dk_pke.inner) ∧
          arrayToBytes dk.z.inner = seedZ seed ∧
          dk.d = some ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).1⟩ ∧
          dk.z = ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).2⟩ ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem768.from_seed_MlKem768MlKem768
    decapsulation_key.DecapsulationKey_MlKem768.generate_deterministic_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem768.new_DecryptionKey_MlKem768DecryptionKey_MlKem768
    module_lattice.maybe_box.MaybeBox_Array_u8_U32.new_Array_u8_U32Array_u8_U32
  step*
  have hd : d = (Model.split (n := 32#usize) (m := 32#usize) seed).1 := by rw [← d_post]
  have hz : z = (Model.split (n := 32#usize) (m := 32#usize) seed).2 := by rw [← d_post]
  refine ⟨⟨ek_post, dk_pke_post⟩, ?_, ?_, by rw [hd], by rw [hz]⟩
  · rw [ek_pke_post, ← dk_pke_post2, hd, seedD_split]
  · rw [hz, seedZ_split]

@[step] theorem ek_export_spec_768 (ek : encapsulation_key.EncapsulationKey_MlKem768) (h : ekInv768 ek) :
    encapsulation_key.EncapsulationKey_MlKem768_KeyExport.to_bytes_MlKem768MlKem768 ek
      ⦃ b => arrayToBytes b = pack (ekPKE768 ek.ek_pke.inner) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem768_KeyExport.to_bytes_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem768_Deref.deref_EncryptionKey_MlKem768EncryptionKey_MlKem768
  have := h.1
  step*

@[step] theorem encapsulate_spec_768 (ek : encapsulation_key.EncapsulationKey_MlKem768) (h : ekInv768 ek)
    (m : Std.Array U8 32#usize) :
    encapsulation_key.EncapsulationKey_MlKem768.encapsulate_deterministic_MlKem768MlKem768 ek m
      ⦃ (c : Std.Array U8 1088#usize) (K : Std.Array U8 32#usize) =>
          Internal.Encaps .ML_KEM_768 (pack (ekPKE768 ek.ek_pke.inner)) (arrayToBytes m) =
            (arrayToBytes K, arrayToBytes c) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem768.encapsulate_deterministic_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem768_Deref.deref_EncryptionKey_MlKem768EncryptionKey_MlKem768
  have := h.1
  step*
  have hG : G (arrayToBytes m ‖ H (pack (ekPKE768 ek.ek_pke.inner))) = (arrayToBytes K, arrayToBytes r) := by
    rw [← h.2]
    refine (G_arrays m ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact K_post.symm
  refine (Internal.Encaps_eq _ _ _ _ (unpack_pack_ekPKE _ _) _ _ hG).trans ?_
  rw [c_post]
  rfl

@[step] theorem decapsulate_spec_768 (dk : decapsulation_key.DecapsulationKey_MlKem768) (h : dkInv768 dk)
    (ct : Std.Array U8 1088#usize) :
    decapsulation_key.DecapsulationKey_MlKem768_Decapsulate.decapsulate_MlKem768MlKem768 dk ct
      ⦃ K => Internal.Decaps .ML_KEM_768 (pack (dk768 dk)) (arrayToBytes ct) = arrayToBytes K ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem768_Decapsulate.decapsulate_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem768_Deref.deref_DecryptionKey_MlKem768DecryptionKey_MlKem768
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32
    encapsulation_key.EncapsulationKey_MlKem768.h_MlKem768MlKem768
    encapsulation_key.EncapsulationKey_MlKem768.ek_pke_MlKem768MlKem768
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem768_Deref.deref_EncryptionKey_MlKem768EncryptionKey_MlKem768
    hybrid_array.Array_u8_U1088_AsRef_Sliceu8.as_ref_u8_U1088U8U1088
    hybrid_array.Array_u8_U1088_Deref.deref_u8_U1088U8U1088
  have := h.1.1
  have := h.2
  step*
  have hG : G (arrayToBytes mp ‖ H (pack (ekPKE768 dk.ek.ek_pke.inner))) = (arrayToBytes Kp, arrayToBytes rp) := by
    rw [← h.1.2]
    refine (G_arrays mp dk.ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact Kp_post.symm
  have hJ : J (arrayToBytes dk.z.inner ‖ arrayToBytes ct) = arrayToBytes Kbar := by
    refine (J_arrays dk.z.inner ct).symm.trans ?_
    rw [← s2_post, Kbar_post, Array.val_to_slice]
  unfold dk768
  refine (Internal.Decaps_eq .ML_KEM_768 (dkPKE768 dk.dk_pke.inner) (pack (ekPKE768 dk.ek.ek_pke.inner))
    (arrayToBytes dk.z.inner) (arrayToBytes ct) _ (unpack_pack_ekPKE _ _) _ mp_post.symm _ _ hG _ hJ).trans ?_
  rw [K_post, c_post]
  exact select_eq (n := 1088#usize) ct cp _ cp_post Kbar Kp

@[step] theorem ek_new_spec_768 (b : Std.Array U8 1184#usize) :
    encapsulation_key.EncapsulationKey_MlKem768.new_MlKem768MlKem768 b
      ⦃ r => match r with
        | .Ok ek => ekInv768 ek ∧ ekPKE768 ek.ek_pke.inner = unpack (arrayToBytes b) ∧
            Encaps.KeyCheck .ML_KEM_768 (arrayToBytes b)
        | .Err _ => Encaps.KeyCheck .ML_KEM_768 (arrayToBytes b) = false ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem768.new_MlKem768MlKem768
  step*

/-! ## ML-KEM-1024 -/

/-- What the Rust code maintains about an encapsulation key: its polynomials are reduced and `h` is
the hash of its encoding. -/
def ekInv1024 (ek : encapsulation_key.EncapsulationKey_MlKem1024) : Prop :=
  Vec.Bounded q ek.ek_pke.inner.t_hat ∧ arrayToBytes ek.h = H (pack (ekPKE1024 ek.ek_pke.inner))

@[step] theorem from_encryption_key_spec_1024 (e : pke.EncryptionKey_MlKem1024) (he : Vec.Bounded q e.t_hat) :
    encapsulation_key.EncapsulationKey_MlKem1024.from_encryption_key_MlKem1024MlKem1024 e
      ⦃ ek => ek.ek_pke.inner = e ∧ ekInv1024 ek ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem1024.from_encryption_key_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem1024.new_EncryptionKey_MlKem1024EncryptionKey_MlKem1024
  step*
  refine ⟨he, h_post.trans ?_⟩
  exact byteVec_fun_congr (fun _ v => H v) (congrArg Vector.toList auu_post)

/-- What the Rust code maintains about a decapsulation key. -/
def dkInv1024 (dk : decapsulation_key.DecapsulationKey_MlKem1024) : Prop :=
  ekInv1024 dk.ek ∧ Vec.Bounded q dk.dk_pke.inner.s_hat

/-- A Rust decapsulation key as the spec's (expanded) one. -/
def dk1024 (dk : decapsulation_key.DecapsulationKey_MlKem1024) : Dk .ML_KEM_1024 :=
  ⟨dkPKE1024 dk.dk_pke.inner, pack (ekPKE1024 dk.ek.ek_pke.inner), H (pack (ekPKE1024 dk.ek.ek_pke.inner)),
    arrayToBytes dk.z.inner⟩

@[step] theorem from_seed_spec_1024 (seed : Std.Array U8 64#usize) :
    decapsulation_key.DecapsulationKey_MlKem1024.from_seed_MlKem1024MlKem1024 seed
      ⦃ dk => dkInv1024 dk ∧
          K_PKE.KeyGen .ML_KEM_1024 (seedD seed) = (ekPKE1024 dk.ek.ek_pke.inner, dkPKE1024 dk.dk_pke.inner) ∧
          arrayToBytes dk.z.inner = seedZ seed ∧
          dk.d = some ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).1⟩ ∧
          dk.z = ⟨(Model.split (n := 32#usize) (m := 32#usize) seed).2⟩ ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem1024.from_seed_MlKem1024MlKem1024
    decapsulation_key.DecapsulationKey_MlKem1024.generate_deterministic_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem1024.new_DecryptionKey_MlKem1024DecryptionKey_MlKem1024
    module_lattice.maybe_box.MaybeBox_Array_u8_U32.new_Array_u8_U32Array_u8_U32
  step*
  have hd : d = (Model.split (n := 32#usize) (m := 32#usize) seed).1 := by rw [← d_post]
  have hz : z = (Model.split (n := 32#usize) (m := 32#usize) seed).2 := by rw [← d_post]
  refine ⟨⟨ek_post, dk_pke_post⟩, ?_, ?_, by rw [hd], by rw [hz]⟩
  · rw [ek_pke_post, ← dk_pke_post2, hd, seedD_split]
  · rw [hz, seedZ_split]

@[step] theorem ek_export_spec_1024 (ek : encapsulation_key.EncapsulationKey_MlKem1024) (h : ekInv1024 ek) :
    encapsulation_key.EncapsulationKey_MlKem1024_KeyExport.to_bytes_MlKem1024MlKem1024 ek
      ⦃ b => arrayToBytes b = pack (ekPKE1024 ek.ek_pke.inner) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem1024_KeyExport.to_bytes_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem1024_Deref.deref_EncryptionKey_MlKem1024EncryptionKey_MlKem1024
  have := h.1
  step*

@[step] theorem encapsulate_spec_1024 (ek : encapsulation_key.EncapsulationKey_MlKem1024) (h : ekInv1024 ek)
    (m : Std.Array U8 32#usize) :
    encapsulation_key.EncapsulationKey_MlKem1024.encapsulate_deterministic_MlKem1024MlKem1024 ek m
      ⦃ (c : Std.Array U8 1568#usize) (K : Std.Array U8 32#usize) =>
          Internal.Encaps .ML_KEM_1024 (pack (ekPKE1024 ek.ek_pke.inner)) (arrayToBytes m) =
            (arrayToBytes K, arrayToBytes c) ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem1024.encapsulate_deterministic_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem1024_Deref.deref_EncryptionKey_MlKem1024EncryptionKey_MlKem1024
  have := h.1
  step*
  have hG : G (arrayToBytes m ‖ H (pack (ekPKE1024 ek.ek_pke.inner))) = (arrayToBytes K, arrayToBytes r) := by
    rw [← h.2]
    refine (G_arrays m ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact K_post.symm
  refine (Internal.Encaps_eq _ _ _ _ (unpack_pack_ekPKE _ _) _ _ hG).trans ?_
  rw [c_post]
  rfl

@[step] theorem decapsulate_spec_1024 (dk : decapsulation_key.DecapsulationKey_MlKem1024) (h : dkInv1024 dk)
    (ct : Std.Array U8 1568#usize) :
    decapsulation_key.DecapsulationKey_MlKem1024_Decapsulate.decapsulate_MlKem1024MlKem1024 dk ct
      ⦃ K => Internal.Decaps .ML_KEM_1024 (pack (dk1024 dk)) (arrayToBytes ct) = arrayToBytes K ⦄ := by
  unfold decapsulation_key.DecapsulationKey_MlKem1024_Decapsulate.decapsulate_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_DecryptionKey_MlKem1024_Deref.deref_DecryptionKey_MlKem1024DecryptionKey_MlKem1024
    module_lattice.maybe_box.MaybeBox_Array_u8_U32_Deref.deref_Array_u8_U32Array_u8_U32
    encapsulation_key.EncapsulationKey_MlKem1024.h_MlKem1024MlKem1024
    encapsulation_key.EncapsulationKey_MlKem1024.ek_pke_MlKem1024MlKem1024
    module_lattice.maybe_box.MaybeBox_EncryptionKey_MlKem1024_Deref.deref_EncryptionKey_MlKem1024EncryptionKey_MlKem1024
    hybrid_array.Array_u8_U1568_AsRef_Sliceu8.as_ref_u8_U1568U8U1568
    hybrid_array.Array_u8_U1568_Deref.deref_u8_U1568U8U1568
  have := h.1.1
  have := h.2
  step*
  have hG : G (arrayToBytes mp ‖ H (pack (ekPKE1024 dk.ek.ek_pke.inner))) = (arrayToBytes Kp, arrayToBytes rp) := by
    rw [← h.1.2]
    refine (G_arrays mp dk.ek.h).symm.trans ?_
    rw [← s_post, ← s1_post]
    exact Kp_post.symm
  have hJ : J (arrayToBytes dk.z.inner ‖ arrayToBytes ct) = arrayToBytes Kbar := by
    refine (J_arrays dk.z.inner ct).symm.trans ?_
    rw [← s2_post, Kbar_post, Array.val_to_slice]
  unfold dk1024
  refine (Internal.Decaps_eq .ML_KEM_1024 (dkPKE1024 dk.dk_pke.inner) (pack (ekPKE1024 dk.ek.ek_pke.inner))
    (arrayToBytes dk.z.inner) (arrayToBytes ct) _ (unpack_pack_ekPKE _ _) _ mp_post.symm _ _ hG _ hJ).trans ?_
  rw [K_post, c_post]
  exact select_eq (n := 1568#usize) ct cp _ cp_post Kbar Kp

@[step] theorem ek_new_spec_1024 (b : Std.Array U8 1568#usize) :
    encapsulation_key.EncapsulationKey_MlKem1024.new_MlKem1024MlKem1024 b
      ⦃ r => match r with
        | .Ok ek => ekInv1024 ek ∧ ekPKE1024 ek.ek_pke.inner = unpack (arrayToBytes b) ∧
            Encaps.KeyCheck .ML_KEM_1024 (arrayToBytes b)
        | .Err _ => Encaps.KeyCheck .ML_KEM_1024 (arrayToBytes b) = false ⦄ := by
  unfold encapsulation_key.EncapsulationKey_MlKem1024.new_MlKem1024MlKem1024
  step*

end MlKem.Properties
