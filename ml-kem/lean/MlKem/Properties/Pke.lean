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

/-! ## ML-KEM-512 -/

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

end MlKem.Properties
