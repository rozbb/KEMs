import MlKem.Properties.Sample
import MlKem.Properties.Ntt
import MlKem.Properties.Compress
import MlKem.Properties.SpecLemmas
import MlKem.Properties.Hash

/-! # K-PKE

The Rust K-PKE (`ml_kem::pke`) matches the spec's K-PKE (§5): key generation, encryption,
decryption, and (de)serialization of the encryption key. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec pack unpack)
open Wychelean.KEM.MLKEM
open RustMlKem
open scoped Wychelean.Notations Wychelean.Utils.Linear

namespace MlKem.Properties

set_option maxRecDepth 20000

/-! ## Glue: the external functions these layers call directly -/

namespace Pke

@[step] theorem typenum_U2_u8 : typenum.uint.U2_Unsigned.U8_U2U1B0 ⦃ r => r = 2#u8 ⦄ := by
  simp [typenum.uint.U2_Unsigned.U8_U2U1B0]

@[step] theorem typenum_U3_u8 : typenum.uint.U3_Unsigned.U8_U3U1B1 ⦃ r => r = 3#u8 ⦄ := by
  simp [typenum.uint.U3_Unsigned.U8_U3U1B1]

@[step] theorem typenum_U4_u8 : typenum.uint.U4_Unsigned.U8_U4U2B0 ⦃ r => r = 4#u8 ⦄ := by
  simp [typenum.uint.U4_Unsigned.U8_U4U2B0]

@[step] theorem index_full_32 (a : Std.Array U8 32#usize) :
    hybrid_array.Array_u8_U32_Index_RangeFull.index_u8_RangeFull_U32U8RangeFullU32 a ()
      ⦃ s => s.val = a.val ⦄ := by
  simp [hybrid_array.Array_u8_U32_Index_RangeFull.index_u8_RangeFull_U32U8RangeFullU32]

/-- Concatenating a Rust array with a list of bytes, as the spec does. -/
theorem bytesOfList_append (a : Std.Array U8 32#usize) (l : List U8) :
    bytesOfList (a.val ++ l) = (arrayToBytes a ‖ bytesOfList l).cast (by simp) := by
  change _ = (arrayToBytes a ++ bytesOfList l).cast _
  apply Vector.ext
  intro i hi
  have ha : a.val.length = 32 := by simp
  simp only [bytesOfList, arrayToBytes, Vector.getElem_cast, Vector.getElem_ofFn, Vector.getElem_append]
  by_cases h : i < 32
  · simp [h, List.getElem_append_left (show i < a.val.length by omega), toByte]
  · simp [h, List.getElem_append_right (show a.val.length ≤ i by omega), ha]

theorem bytesOfList_singleton (x : U8) : bytesOfList [x] = #v[toByte x] := by
  apply Vector.ext; intro i hi
  have : i = 0 := by simp at hi; omega
  subst this; simp [bytesOfList]

theorem arrayToBytes_concat {n m k : Usize} (a : Std.Array U8 n) (b : Std.Array U8 m)
    (h : n.val + m.val = k.val) :
    arrayToBytes (Model.concat a b h) = (arrayToBytes a ‖ arrayToBytes b).cast h := by
  change _ = (arrayToBytes a ++ arrayToBytes b).cast h
  apply Vector.ext
  intro i hi
  simp only [arrayToBytes, Model.concat, Vector.getElem_cast, Vector.getElem_ofFn, Vector.getElem_append]
  by_cases hin : i < n.val
  · simp [hin, List.getElem_append_left (show i < a.val.length by simp; omega)]
  · simp [hin, List.getElem_append_right (show a.val.length ≤ i by simp; omega)]

theorem arrayToBytes_split {n m k : Usize} (a : Std.Array U8 k) (h : n.val + m.val = k.val) :
    (arrayToBytes (Model.split (n := n) (m := m) a h).1, arrayToBytes (Model.split (n := n) (m := m) a h).2)
      = Wychelean.split (arrayToBytes a) n.val m.val h.symm := by
  simp only [Wychelean.split, Prod.mk.injEq]
  constructor <;> apply Vector.ext <;> intro i hi <;>
    simp [arrayToBytes, Model.split, Wychelean.slice, Array.from_val]

theorem arrayToBytes_inj {n : Usize} (a b : Std.Array U8 n) : arrayToBytes a = arrayToBytes b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg Vector.toList h
  simp only [toList_arrayToBytes] at h'
  have hinj : Function.Injective toByte := fun x y hxy => by
    have := congrArg UInt8.toBitVec hxy
    cases x; cases y; simp only [toByte] at this; subst this; rfl
  exact Aeneas.Std.Array.ext _ _ (List.map_injective_iff.mpr hinj h')

@[step] theorem split_ct_512 (c : Std.Array U8 768#usize) :
    param.MlKem512_PkeParams.split_ct_MlKem512MlKem512 c
      ⦃ (c1 : Std.Array U8 640#usize) (c2 : Std.Array U8 128#usize) =>
          (arrayToBytes c1, arrayToBytes c2) =
            Wychelean.split (arrayToBytes c : ByteVec (ctLen .ML_KEM_512)) (c₁Len .ML_KEM_512)
              (c₂Len .ML_KEM_512) ⦄ := by
  simp only [param.MlKem512_PkeParams.split_ct_MlKem512MlKem512,
    hybrid_array.Array_u8_U768.split_ref_u8_U768_U640U8U768U640, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split c _

@[step] theorem split_ek_512 (b : Std.Array U8 800#usize) :
    param.MlKem512_PkeParams.split_ek_MlKem512MlKem512 b
      ⦃ (t : Std.Array U8 768#usize) (ρ : Std.Array U8 32#usize) =>
          (arrayToBytes t, arrayToBytes ρ) =
            Wychelean.split (arrayToBytes b : ByteVec (ekLen .ML_KEM_512)) (vecLen .ML_KEM_512)
              seedLen ⦄ := by
  simp only [param.MlKem512_PkeParams.split_ek_MlKem512MlKem512,
    hybrid_array.Array_u8_U800.split_ref_u8_U800_U768U8U800U768, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split b _

@[step] theorem concat_ek_512 (t : Std.Array U8 768#usize) (ρ : Std.Array U8 32#usize) :
    param.MlKem512_PkeParams.concat_ek_MlKem512MlKem512 t ρ
      ⦃ b => arrayToBytes b = (arrayToBytes t ‖ arrayToBytes ρ).cast (by simp) ⦄ := by
  simp [param.MlKem512_PkeParams.concat_ek_MlKem512MlKem512,
    hybrid_array.Array_u8_U768.concat_u8_U768_U32U8U768U32, arrayToBytes_concat]

@[step] theorem split_ct_768 (c : Std.Array U8 1088#usize) :
    param.MlKem768_PkeParams.split_ct_MlKem768MlKem768 c
      ⦃ (c1 : Std.Array U8 960#usize) (c2 : Std.Array U8 128#usize) =>
          (arrayToBytes c1, arrayToBytes c2) =
            Wychelean.split (arrayToBytes c : ByteVec (ctLen .ML_KEM_768)) (c₁Len .ML_KEM_768)
              (c₂Len .ML_KEM_768) ⦄ := by
  simp only [param.MlKem768_PkeParams.split_ct_MlKem768MlKem768,
    hybrid_array.Array_u8_U1088.split_ref_u8_U1088_U960U8U1088U960, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split c _

@[step] theorem split_ek_768 (b : Std.Array U8 1184#usize) :
    param.MlKem768_PkeParams.split_ek_MlKem768MlKem768 b
      ⦃ (t : Std.Array U8 1152#usize) (ρ : Std.Array U8 32#usize) =>
          (arrayToBytes t, arrayToBytes ρ) =
            Wychelean.split (arrayToBytes b : ByteVec (ekLen .ML_KEM_768)) (vecLen .ML_KEM_768)
              seedLen ⦄ := by
  simp only [param.MlKem768_PkeParams.split_ek_MlKem768MlKem768,
    hybrid_array.Array_u8_U1184.split_ref_u8_U1184_U1152U8U1184U1152, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split b _

@[step] theorem concat_ek_768 (t : Std.Array U8 1152#usize) (ρ : Std.Array U8 32#usize) :
    param.MlKem768_PkeParams.concat_ek_MlKem768MlKem768 t ρ
      ⦃ b => arrayToBytes b = (arrayToBytes t ‖ arrayToBytes ρ).cast (by simp) ⦄ := by
  simp [param.MlKem768_PkeParams.concat_ek_MlKem768MlKem768,
    hybrid_array.Array_u8_U1152.concat_u8_U1152_U32U8U1152U32, arrayToBytes_concat]

@[step] theorem split_ct_1024 (c : Std.Array U8 1568#usize) :
    param.MlKem1024_PkeParams.split_ct_MlKem1024MlKem1024 c
      ⦃ (c1 : Std.Array U8 1408#usize) (c2 : Std.Array U8 160#usize) =>
          (arrayToBytes c1, arrayToBytes c2) =
            Wychelean.split (arrayToBytes c : ByteVec (ctLen .ML_KEM_1024)) (c₁Len .ML_KEM_1024)
              (c₂Len .ML_KEM_1024) ⦄ := by
  simp only [param.MlKem1024_PkeParams.split_ct_MlKem1024MlKem1024,
    hybrid_array.Array_u8_U1568.split_ref_u8_U1568_U1408U8U1568U1408, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split c _

@[step] theorem split_ek_1024 (b : Std.Array U8 1568#usize) :
    param.MlKem1024_PkeParams.split_ek_MlKem1024MlKem1024 b
      ⦃ (t : Std.Array U8 1536#usize) (ρ : Std.Array U8 32#usize) =>
          (arrayToBytes t, arrayToBytes ρ) =
            Wychelean.split (arrayToBytes b : ByteVec (ekLen .ML_KEM_1024)) (vecLen .ML_KEM_1024)
              seedLen ⦄ := by
  simp only [param.MlKem1024_PkeParams.split_ek_MlKem1024MlKem1024,
    hybrid_array.Array_u8_U1568.split_ref_u8_U1568_U1536U8U1568U1536, WP.spec_ok, WP.uncurry'_eq]
  exact arrayToBytes_split b _

@[step] theorem concat_ek_1024 (t : Std.Array U8 1536#usize) (ρ : Std.Array U8 32#usize) :
    param.MlKem1024_PkeParams.concat_ek_MlKem1024MlKem1024 t ρ
      ⦃ b => arrayToBytes b = (arrayToBytes t ‖ arrayToBytes ρ).cast (by simp) ⦄ := by
  simp [param.MlKem1024_PkeParams.concat_ek_MlKem1024MlKem1024,
    hybrid_array.Array_u8_U1536.concat_u8_U1536_U32U8U1536U32, arrayToBytes_concat]

@[step] theorem clone_32 (a : Std.Array U8 32#usize) :
    hybrid_array.Array_u8_U32_Clone.clone_u8_U32U8U32 a ⦃ b => b = a ⦄ := by
  simp [hybrid_array.Array_u8_U32_Clone.clone_u8_U32U8U32]

@[step] theorem eq_800 (a b : Std.Array U8 800#usize) :
    hybrid_array.Array_u8_U800_PartialEq_Array_u8_U800.eq_u8_U800U8U800 a b ⦃ r => r = decide (a = b) ⦄ := by
  simp [hybrid_array.Array_u8_U800_PartialEq_Array_u8_U800.eq_u8_U800U8U800]

@[step] theorem concat_ct_512 (u : Std.Array U8 640#usize) (v : Std.Array U8 128#usize) :
    param.MlKem512_PkeParams.concat_ct_MlKem512MlKem512 u v
      ⦃ c => arrayToBytes c = (arrayToBytes u ‖ arrayToBytes v).cast (by simp) ⦄ := by
  simp [param.MlKem512_PkeParams.concat_ct_MlKem512MlKem512,
    hybrid_array.Array_u8_U640.concat_u8_U640_U128U8U640U128, arrayToBytes_concat]

@[step] theorem eq_1184 (a b : Std.Array U8 1184#usize) :
    hybrid_array.Array_u8_U1184_PartialEq_Array_u8_U1184.eq_u8_U1184U8U1184 a b ⦃ r => r = decide (a = b) ⦄ := by
  simp [hybrid_array.Array_u8_U1184_PartialEq_Array_u8_U1184.eq_u8_U1184U8U1184]

@[step] theorem concat_ct_768 (u : Std.Array U8 960#usize) (v : Std.Array U8 128#usize) :
    param.MlKem768_PkeParams.concat_ct_MlKem768MlKem768 u v
      ⦃ c => arrayToBytes c = (arrayToBytes u ‖ arrayToBytes v).cast (by simp) ⦄ := by
  simp [param.MlKem768_PkeParams.concat_ct_MlKem768MlKem768,
    hybrid_array.Array_u8_U960.concat_u8_U960_U128U8U960U128, arrayToBytes_concat]

@[step] theorem eq_1568 (a b : Std.Array U8 1568#usize) :
    hybrid_array.Array_u8_U1568_PartialEq_Array_u8_U1568.eq_u8_U1568U8U1568 a b ⦃ r => r = decide (a = b) ⦄ := by
  simp [hybrid_array.Array_u8_U1568_PartialEq_Array_u8_U1568.eq_u8_U1568U8U1568]

@[step] theorem concat_ct_1024 (u : Std.Array U8 1408#usize) (v : Std.Array U8 160#usize) :
    param.MlKem1024_PkeParams.concat_ct_MlKem1024MlKem1024 u v
      ⦃ c => arrayToBytes c = (arrayToBytes u ‖ arrayToBytes v).cast (by simp) ⦄ := by
  simp [param.MlKem1024_PkeParams.concat_ct_MlKem1024MlKem1024,
    hybrid_array.Array_u8_U1408.concat_u8_U1408_U160U8U1408U160, arrayToBytes_concat]

theorem toByte_eq (x : U8) : toByte x = UInt8.ofNat x.val := by
  apply UInt8.toBitVec_inj.mp
  change x.bv = BitVec.ofNat 8 x.bv.toNat
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.bv.isLt]

theorem unpack_ciphertext (p : ParameterSet) (b : ByteVec (ctLen p)) :
    (unpack b : Ciphertext p) =
      ⟨PolyVector.ByteDecode (dᵤ p) (Wychelean.split b (c₁Len p) (c₂Len p)).1,
        ⟨ByteDecode (Wychelean.split b (c₁Len p) (c₂Len p)).2⟩⟩ := rfl

theorem pack_ciphertext (p : ParameterSet) (u : PolyVector (m (dᵤ p)) (Wychelean.KEM.MLKEM.k p))
    (v : Wychelean.KEM.MLKEM.Polynomial (m (dᵥ p))) :
    pack (⟨u, v⟩ : Ciphertext p) = PolyVector.ByteEncode (dᵤ p) u ‖ ByteEncode (dᵥ p) v.coeffs := rfl

theorem unpack_ciphertext_of_split (p : ParameterSet) (b : ByteVec (ctLen p)) (x : ByteVec (c₁Len p))
    (y : ByteVec (c₂Len p)) (h : (x, y) = Wychelean.split b (c₁Len p) (c₂Len p)) :
    (unpack b : Ciphertext p) = ⟨PolyVector.ByteDecode (dᵤ p) x, ⟨ByteDecode y⟩⟩ := by
  rw [unpack_ciphertext, ← h]

theorem pack_ekPKE (p : ParameterSet) (e : EkPKE p) :
    pack e = ByteEncode₁₂ e.«t̂» ‖ e.ρ := rfl

theorem unpack_ekPKE_of_split (p : ParameterSet) (b : ByteVec (ekLen p)) (x : ByteVec (vecLen p))
    (y : ByteVec seedLen) (h : (x, y) = Wychelean.split b (vecLen p) seedLen) :
    (unpack b : EkPKE p) = ⟨ByteDecode₁₂ x, y⟩ := by
  change (let (t, ρ) := Wychelean.split b (vecLen p) seedLen; (⟨ByteDecode₁₂ t, ρ⟩ : EkPKE p)) = _
  rw [← h]

theorem keyCheck_eq (p : ParameterSet) (b : ByteVec (ekLen p)) (e : EkPKE p) (he : e = unpack b)
    (x : ByteVec (ekLen p)) (hx : x = pack e) : Encaps.KeyCheck p b = decide (x = b) := by
  subst he hx; rfl

/-- `K_PKE.KeyGen_eq`, with the hash already evaluated. -/
theorem KeyGen_of_G (p : ParameterSet) (d : ByteVec 32) (ρ σ : ByteVec 32)
    (h : G (d ‖ #v[UInt8.ofNat (Wychelean.KEM.MLKEM.k p)]) = (ρ, σ)) :
    K_PKE.KeyGen p d =
      (⟨Wychelean.Utils.Linear.Mat.mulVec (sampleMatrix (Wychelean.KEM.MLKEM.k p) ρ)
          (PolyVector.NTT (Vector.ofFn fun i : Fin (Wychelean.KEM.MLKEM.k p) =>
            SamplePolyCBD (η := η₁ p) (PRF (η₁ p) σ (UInt8.ofNat i)))) +
        PolyVector.NTT (Vector.ofFn fun i : Fin (Wychelean.KEM.MLKEM.k p) =>
            SamplePolyCBD (η := η₁ p) (PRF (η₁ p) σ (UInt8.ofNat (Wychelean.KEM.MLKEM.k p + i)))), ρ⟩,
       ⟨PolyVector.NTT (Vector.ofFn fun i : Fin (Wychelean.KEM.MLKEM.k p) =>
            SamplePolyCBD (η := η₁ p) (PRF (η₁ p) σ (UInt8.ofNat i)))⟩) := by
  rw [K_PKE.KeyGen_eq, h]

end Pke

open Pke

/-! ## Per parameter set

The same proofs for each parameter set, generated from those for ML-KEM-512. -/

/-! ### ML-KEM-512 -/

/-- A Rust K-PKE encryption key, as the spec's. -/
def ekPKE512 (ek : pke.EncryptionKey_MlKem512) : EkPKE .ML_KEM_512 :=
  ⟨toNTTVec ek.t_hat, arrayToBytes ek.rho⟩

/-- A Rust K-PKE decryption key, as the spec's. -/
def dkPKE512 (dk : pke.DecryptionKey_MlKem512) : DkPKE .ML_KEM_512 := ⟨toNTTVec dk.s_hat⟩

@[step] theorem generate_spec_512 (d : Std.Array U8 32#usize) :
    pke.DecryptionKey_MlKem512.generate_MlKem512MlKem512 d
      ⦃ (dk : pke.DecryptionKey_MlKem512) (ek : pke.EncryptionKey_MlKem512) =>
          Vec.Bounded q dk.s_hat ∧ Vec.Bounded q ek.t_hat ∧
          K_PKE.KeyGen .ML_KEM_512 (arrayToBytes d) = (ekPKE512 ek, dkPKE512 dk) ⦄ := by
  unfold pke.DecryptionKey_MlKem512.generate_MlKem512MlKem512
  step*
  refine ⟨s_hat_post, t_hat_post, ?_⟩
  have hs1 : s1.val = [2#u8] := by rw [s1_post, k_post]; simp
  have hG : G (arrayToBytes d ‖ #v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_512)])
      = (arrayToBytes rho, arrayToBytes sigma) := by
    have h2 : (#v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_512)] : Vector UInt8 1) = #v[toByte 2#u8] := rfl
    rw [h2, rho_post, s_post, hs1, bytesOfList_append, G_cast, bytesOfList_singleton]
  have hk : (k.val : ℕ) = 2 := by rw [k_post]; rfl
  refine (KeyGen_of_G _ _ _ _ hG).trans ?_
  simp only [ekPKE512, dkPKE512, Prod.mk.injEq, EkPKE.mk.injEq, DkPKE.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · rw [t_hat_post1, nvbfu_post1, A_hat_post1, s_hat_post1, e_hat_post1, s2_post1, e_post1, hk]
    simp only [Bool.false_eq_true, if_false, Nat.zero_add]
    rfl
  · rw [s_hat_post1, s2_post1]
    simp only [Nat.zero_add]
    rfl

@[step] theorem encrypt_spec_512 (ek : pke.EncryptionKey_MlKem512) (msg r : Std.Array U8 32#usize)
    (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem512.encrypt_MlKem512MlKem512 ek msg r
      ⦃ c => arrayToBytes c =
          pack (K_PKE.Encrypt .ML_KEM_512 (ekPKE512 ek) (arrayToBytes msg) (arrayToBytes r)) ⦄ := by
  unfold pke.EncryptionKey_MlKem512.encrypt_MlKem512MlKem512
  step*
  refine c_post.trans ?_
  rw [K_PKE.Encrypt_eq]
  simp only [pack_ciphertext]
  subst vbfu_post pbf1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  have hpbf : Coeffs.toVector (m 4) pbf1 = (Coeffs.toPoly (m 4) pbf1).coeffs := rfl
  simp only [c1_post, c2_post, vbfu_post2, hpbf, pbf1_post2, u_post1, ATr_post1, nvbfu_post1,
    A_hat_t_post1, r_hat_post1, r_post1, e1_post1, v_post1, pbf_post1, tTr_post1, npbf_post1, __post2,
    e2_post1, prf_output_post, i_post, ekPKE512, if_true, Nat.zero_add, toByte_eq]
  have h2 : ((2#u8 : U8).val : ℕ) = 2 := rfl
  have hi1 : i1.val = 4 := by rw [i1_post, i_post]; rfl
  simp only [h2, hi1, Coeffs.toPoly, mu_post1]
  rfl

@[step] theorem decrypt_spec_512 (dk : pke.DecryptionKey_MlKem512) (c : Std.Array U8 768#usize)
    (hdk : Vec.Bounded q dk.s_hat) :
    pke.DecryptionKey_MlKem512.decrypt_MlKem512MlKem512 dk c
      ⦃ msg => arrayToBytes msg = K_PKE.Decrypt .ML_KEM_512 (dkPKE512 dk) (unpack (arrayToBytes c)) ⦄ := by
  unfold pke.DecryptionKey_MlKem512.decrypt_MlKem512MlKem512
  step*
  subst_vars
  have hc1 := (congrArg Prod.fst c1_post).symm
  have hc2 := (congrArg Prod.snd c1_post).symm
  have hct : (unpack (arrayToBytes c) : Ciphertext .ML_KEM_512) =
      ⟨PolyVector.ByteDecode 10 (arrayToBytes c1), ⟨ByteDecode (arrayToBytes c2)⟩⟩ := by
    exact unpack_ciphertext_of_split _ _ _ _ c1_post
  rw [msg_post, hct]
  simp only [K_PKE.Decrypt, dkPKE512]
  clear hct hc1 hc2 c1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  change (ByteEncode 1 (Coeffs.toPoly (m 1) _).coeffs _).toList = _
  simp only [*]
  simp only [Coeffs.toPoly, v_post1]
  rfl

@[step] theorem ek_to_bytes_spec_512 (ek : pke.EncryptionKey_MlKem512) (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem512.to_bytes_MlKem512MlKem512 ek
      ⦃ b => arrayToBytes b = pack (ekPKE512 ek) ⦄ := by
  unfold pke.EncryptionKey_MlKem512.to_bytes_MlKem512MlKem512
  step*
  refine b_post.trans ?_
  rw [pack_ekPKE]
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast, t_hat_post, ekPKE512, auu_post, toList_vector_append]
  exact (toList_vector_append _ _).symm

@[step] theorem ek_from_bytes_spec_512 (enc : Std.Array U8 800#usize) :
    pke.EncryptionKey_MlKem512.from_bytes_MlKem512MlKem512 enc
      ⦃ r => match r with
        | .Ok ek => Vec.Bounded q ek.t_hat ∧ ekPKE512 ek = unpack (arrayToBytes enc) ∧
            Encaps.KeyCheck .ML_KEM_512 (arrayToBytes enc)
        | .Err _ => Encaps.KeyCheck .ML_KEM_512 (arrayToBytes enc) = false ⦄ := by
  unfold pke.EncryptionKey_MlKem512.from_bytes_MlKem512MlKem512
  step*
  all_goals
    have hek : ekPKE512 { t_hat := t_hat1, rho := auu } = unpack (arrayToBytes enc) := by
      refine Eq.trans ?_ (unpack_ekPKE_of_split _ _ _ _ t_hat_post).symm
      simp only [ekPKE512, t_hat1_post1, auu_post]
    have hkc : Encaps.KeyCheck .ML_KEM_512 (arrayToBytes enc) = decide (auu1 = enc) := by
      refine (keyCheck_eq _ _ _ hek _ auu1_post).trans ?_
      exact decide_eq_decide.mpr (arrayToBytes_inj _ _)
  · rename_i hb
    refine ⟨t_hat1_post, hek, ?_⟩
    rw [hkc, ← b_post]
    exact hb
  · rename_i hb
    rw [hkc, ← b_post]
    exact Bool.eq_false_iff.mpr hb

/-! ### ML-KEM-768 -/

/-- A Rust K-PKE encryption key, as the spec's. -/
def ekPKE768 (ek : pke.EncryptionKey_MlKem768) : EkPKE .ML_KEM_768 :=
  ⟨toNTTVec ek.t_hat, arrayToBytes ek.rho⟩

/-- A Rust K-PKE decryption key, as the spec's. -/
def dkPKE768 (dk : pke.DecryptionKey_MlKem768) : DkPKE .ML_KEM_768 := ⟨toNTTVec dk.s_hat⟩

@[step] theorem generate_spec_768 (d : Std.Array U8 32#usize) :
    pke.DecryptionKey_MlKem768.generate_MlKem768MlKem768 d
      ⦃ (dk : pke.DecryptionKey_MlKem768) (ek : pke.EncryptionKey_MlKem768) =>
          Vec.Bounded q dk.s_hat ∧ Vec.Bounded q ek.t_hat ∧
          K_PKE.KeyGen .ML_KEM_768 (arrayToBytes d) = (ekPKE768 ek, dkPKE768 dk) ⦄ := by
  unfold pke.DecryptionKey_MlKem768.generate_MlKem768MlKem768
  step*
  refine ⟨s_hat_post, t_hat_post, ?_⟩
  have hs1 : s1.val = [3#u8] := by rw [s1_post, k_post]; simp
  have hG : G (arrayToBytes d ‖ #v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_768)])
      = (arrayToBytes rho, arrayToBytes sigma) := by
    have h2 : (#v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_768)] : Vector UInt8 1) = #v[toByte 3#u8] := rfl
    rw [h2, rho_post, s_post, hs1, bytesOfList_append, G_cast, bytesOfList_singleton]
  have hk : (k.val : ℕ) = 3 := by rw [k_post]; rfl
  refine (KeyGen_of_G _ _ _ _ hG).trans ?_
  simp only [ekPKE768, dkPKE768, Prod.mk.injEq, EkPKE.mk.injEq, DkPKE.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · rw [t_hat_post1, nvbfu_post1, A_hat_post1, s_hat_post1, e_hat_post1, s2_post1, e_post1, hk]
    simp only [Bool.false_eq_true, if_false, Nat.zero_add]
    rfl
  · rw [s_hat_post1, s2_post1]
    simp only [Nat.zero_add]
    rfl

@[step] theorem encrypt_spec_768 (ek : pke.EncryptionKey_MlKem768) (msg r : Std.Array U8 32#usize)
    (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem768.encrypt_MlKem768MlKem768 ek msg r
      ⦃ c => arrayToBytes c =
          pack (K_PKE.Encrypt .ML_KEM_768 (ekPKE768 ek) (arrayToBytes msg) (arrayToBytes r)) ⦄ := by
  unfold pke.EncryptionKey_MlKem768.encrypt_MlKem768MlKem768
  step*
  refine c_post.trans ?_
  rw [K_PKE.Encrypt_eq]
  simp only [pack_ciphertext]
  subst vbfu_post pbf1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  have hpbf : Coeffs.toVector (m 4) pbf1 = (Coeffs.toPoly (m 4) pbf1).coeffs := rfl
  simp only [c1_post, c2_post, vbfu_post2, hpbf, pbf1_post2, u_post1, ATr_post1, nvbfu_post1,
    A_hat_t_post1, r_hat_post1, r_post1, e1_post1, v_post1, pbf_post1, tTr_post1, npbf_post1, __post2,
    e2_post1, prf_output_post, i_post, ekPKE768, if_true, Nat.zero_add, toByte_eq]
  have h2 : ((3#u8 : U8).val : ℕ) = 3 := rfl
  have hi1 : i1.val = 6 := by rw [i1_post, i_post]; rfl
  simp only [h2, hi1, Coeffs.toPoly, mu_post1]
  rfl

@[step] theorem decrypt_spec_768 (dk : pke.DecryptionKey_MlKem768) (c : Std.Array U8 1088#usize)
    (hdk : Vec.Bounded q dk.s_hat) :
    pke.DecryptionKey_MlKem768.decrypt_MlKem768MlKem768 dk c
      ⦃ msg => arrayToBytes msg = K_PKE.Decrypt .ML_KEM_768 (dkPKE768 dk) (unpack (arrayToBytes c)) ⦄ := by
  unfold pke.DecryptionKey_MlKem768.decrypt_MlKem768MlKem768
  step*
  subst_vars
  have hc1 := (congrArg Prod.fst c1_post).symm
  have hc2 := (congrArg Prod.snd c1_post).symm
  have hct : (unpack (arrayToBytes c) : Ciphertext .ML_KEM_768) =
      ⟨PolyVector.ByteDecode 10 (arrayToBytes c1), ⟨ByteDecode (arrayToBytes c2)⟩⟩ := by
    exact unpack_ciphertext_of_split _ _ _ _ c1_post
  rw [msg_post, hct]
  simp only [K_PKE.Decrypt, dkPKE768]
  clear hct hc1 hc2 c1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  change (ByteEncode 1 (Coeffs.toPoly (m 1) _).coeffs _).toList = _
  simp only [*]
  simp only [Coeffs.toPoly, v_post1]
  rfl

@[step] theorem ek_to_bytes_spec_768 (ek : pke.EncryptionKey_MlKem768) (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem768.to_bytes_MlKem768MlKem768 ek
      ⦃ b => arrayToBytes b = pack (ekPKE768 ek) ⦄ := by
  unfold pke.EncryptionKey_MlKem768.to_bytes_MlKem768MlKem768
  step*
  refine b_post.trans ?_
  rw [pack_ekPKE]
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast, t_hat_post, ekPKE768, auu_post, toList_vector_append]
  exact (toList_vector_append _ _).symm

@[step] theorem ek_from_bytes_spec_768 (enc : Std.Array U8 1184#usize) :
    pke.EncryptionKey_MlKem768.from_bytes_MlKem768MlKem768 enc
      ⦃ r => match r with
        | .Ok ek => Vec.Bounded q ek.t_hat ∧ ekPKE768 ek = unpack (arrayToBytes enc) ∧
            Encaps.KeyCheck .ML_KEM_768 (arrayToBytes enc)
        | .Err _ => Encaps.KeyCheck .ML_KEM_768 (arrayToBytes enc) = false ⦄ := by
  unfold pke.EncryptionKey_MlKem768.from_bytes_MlKem768MlKem768
  step*
  all_goals
    have hek : ekPKE768 { t_hat := t_hat1, rho := auu } = unpack (arrayToBytes enc) := by
      refine Eq.trans ?_ (unpack_ekPKE_of_split _ _ _ _ t_hat_post).symm
      simp only [ekPKE768, t_hat1_post1, auu_post]
    have hkc : Encaps.KeyCheck .ML_KEM_768 (arrayToBytes enc) = decide (auu1 = enc) := by
      refine (keyCheck_eq _ _ _ hek _ auu1_post).trans ?_
      exact decide_eq_decide.mpr (arrayToBytes_inj _ _)
  · rename_i hb
    refine ⟨t_hat1_post, hek, ?_⟩
    rw [hkc, ← b_post]
    exact hb
  · rename_i hb
    rw [hkc, ← b_post]
    exact Bool.eq_false_iff.mpr hb

/-! ### ML-KEM-1024 -/

/-- A Rust K-PKE encryption key, as the spec's. -/
def ekPKE1024 (ek : pke.EncryptionKey_MlKem1024) : EkPKE .ML_KEM_1024 :=
  ⟨toNTTVec ek.t_hat, arrayToBytes ek.rho⟩

/-- A Rust K-PKE decryption key, as the spec's. -/
def dkPKE1024 (dk : pke.DecryptionKey_MlKem1024) : DkPKE .ML_KEM_1024 := ⟨toNTTVec dk.s_hat⟩

@[step] theorem generate_spec_1024 (d : Std.Array U8 32#usize) :
    pke.DecryptionKey_MlKem1024.generate_MlKem1024MlKem1024 d
      ⦃ (dk : pke.DecryptionKey_MlKem1024) (ek : pke.EncryptionKey_MlKem1024) =>
          Vec.Bounded q dk.s_hat ∧ Vec.Bounded q ek.t_hat ∧
          K_PKE.KeyGen .ML_KEM_1024 (arrayToBytes d) = (ekPKE1024 ek, dkPKE1024 dk) ⦄ := by
  unfold pke.DecryptionKey_MlKem1024.generate_MlKem1024MlKem1024
  step*
  refine ⟨s_hat_post, t_hat_post, ?_⟩
  have hs1 : s1.val = [4#u8] := by rw [s1_post, k_post]; simp
  have hG : G (arrayToBytes d ‖ #v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_1024)])
      = (arrayToBytes rho, arrayToBytes sigma) := by
    have h2 : (#v[UInt8.ofNat ↑(Wychelean.KEM.MLKEM.k .ML_KEM_1024)] : Vector UInt8 1) = #v[toByte 4#u8] := rfl
    rw [h2, rho_post, s_post, hs1, bytesOfList_append, G_cast, bytesOfList_singleton]
  have hk : (k.val : ℕ) = 4 := by rw [k_post]; rfl
  refine (KeyGen_of_G _ _ _ _ hG).trans ?_
  simp only [ekPKE1024, dkPKE1024, Prod.mk.injEq, EkPKE.mk.injEq, DkPKE.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · rw [t_hat_post1, nvbfu_post1, A_hat_post1, s_hat_post1, e_hat_post1, s2_post1, e_post1, hk]
    simp only [Bool.false_eq_true, if_false, Nat.zero_add]
    rfl
  · rw [s_hat_post1, s2_post1]
    simp only [Nat.zero_add]
    rfl

@[step] theorem encrypt_spec_1024 (ek : pke.EncryptionKey_MlKem1024) (msg r : Std.Array U8 32#usize)
    (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem1024.encrypt_MlKem1024MlKem1024 ek msg r
      ⦃ c => arrayToBytes c =
          pack (K_PKE.Encrypt .ML_KEM_1024 (ekPKE1024 ek) (arrayToBytes msg) (arrayToBytes r)) ⦄ := by
  unfold pke.EncryptionKey_MlKem1024.encrypt_MlKem1024MlKem1024
  step*
  refine c_post.trans ?_
  rw [K_PKE.Encrypt_eq]
  simp only [pack_ciphertext]
  subst vbfu_post pbf1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  have hpbf : Coeffs.toVector (m 5) pbf1 = (Coeffs.toPoly (m 5) pbf1).coeffs := rfl
  simp only [c1_post, c2_post, vbfu_post2, hpbf, pbf1_post2, u_post1, ATr_post1, nvbfu_post1,
    A_hat_t_post1, r_hat_post1, r_post1, e1_post1, v_post1, pbf_post1, tTr_post1, npbf_post1, __post2,
    e2_post1, prf_output_post, i_post, ekPKE1024, if_true, Nat.zero_add, toByte_eq]
  have h2 : ((4#u8 : U8).val : ℕ) = 4 := rfl
  have hi1 : i1.val = 8 := by rw [i1_post, i_post]; rfl
  simp only [h2, hi1, Coeffs.toPoly, mu_post1]
  rfl

@[step] theorem decrypt_spec_1024 (dk : pke.DecryptionKey_MlKem1024) (c : Std.Array U8 1568#usize)
    (hdk : Vec.Bounded q dk.s_hat) :
    pke.DecryptionKey_MlKem1024.decrypt_MlKem1024MlKem1024 dk c
      ⦃ msg => arrayToBytes msg = K_PKE.Decrypt .ML_KEM_1024 (dkPKE1024 dk) (unpack (arrayToBytes c)) ⦄ := by
  unfold pke.DecryptionKey_MlKem1024.decrypt_MlKem1024MlKem1024
  step*
  subst_vars
  have hc1 := (congrArg Prod.fst c1_post).symm
  have hc2 := (congrArg Prod.snd c1_post).symm
  have hct : (unpack (arrayToBytes c) : Ciphertext .ML_KEM_1024) =
      ⟨PolyVector.ByteDecode 11 (arrayToBytes c1), ⟨ByteDecode (arrayToBytes c2)⟩⟩ := by
    exact unpack_ciphertext_of_split _ _ _ _ c1_post
  rw [msg_post, hct]
  simp only [K_PKE.Decrypt, dkPKE1024]
  clear hct hc1 hc2 c1_post
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast]
  change (ByteEncode 1 (Coeffs.toPoly (m 1) _).coeffs _).toList = _
  simp only [*]
  simp only [Coeffs.toPoly, v_post1]
  rfl

@[step] theorem ek_to_bytes_spec_1024 (ek : pke.EncryptionKey_MlKem1024) (hek : Vec.Bounded q ek.t_hat) :
    pke.EncryptionKey_MlKem1024.to_bytes_MlKem1024MlKem1024 ek
      ⦃ b => arrayToBytes b = pack (ekPKE1024 ek) ⦄ := by
  unfold pke.EncryptionKey_MlKem1024.to_bytes_MlKem1024MlKem1024
  step*
  refine b_post.trans ?_
  rw [pack_ekPKE]
  apply Vector.toList_inj.mp
  simp only [Vector.toList_cast, t_hat_post, ekPKE1024, auu_post, toList_vector_append]
  exact (toList_vector_append _ _).symm

@[step] theorem ek_from_bytes_spec_1024 (enc : Std.Array U8 1568#usize) :
    pke.EncryptionKey_MlKem1024.from_bytes_MlKem1024MlKem1024 enc
      ⦃ r => match r with
        | .Ok ek => Vec.Bounded q ek.t_hat ∧ ekPKE1024 ek = unpack (arrayToBytes enc) ∧
            Encaps.KeyCheck .ML_KEM_1024 (arrayToBytes enc)
        | .Err _ => Encaps.KeyCheck .ML_KEM_1024 (arrayToBytes enc) = false ⦄ := by
  unfold pke.EncryptionKey_MlKem1024.from_bytes_MlKem1024MlKem1024
  step*
  all_goals
    have hek : ekPKE1024 { t_hat := t_hat1, rho := auu } = unpack (arrayToBytes enc) := by
      refine Eq.trans ?_ (unpack_ekPKE_of_split _ _ _ _ t_hat_post).symm
      simp only [ekPKE1024, t_hat1_post1, auu_post]
    have hkc : Encaps.KeyCheck .ML_KEM_1024 (arrayToBytes enc) = decide (auu1 = enc) := by
      refine (keyCheck_eq _ _ _ hek _ auu1_post).trans ?_
      exact decide_eq_decide.mpr (arrayToBytes_inj _ _)
  · rename_i hb
    refine ⟨t_hat1_post, hek, ?_⟩
    rw [hkc, ← b_post]
    exact hb
  · rename_i hb
    rw [hkc, ← b_post]
    exact Bool.eq_false_iff.mpr hb

end MlKem.Properties
