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

/-! ## Helpers: converting between Rust byte containers and spec byte vectors -/

theorem toList_arrayToBytes {n : Usize} (a : Std.Array U8 n) :
    (arrayToBytes a).toList = a.val.map toByte := by
  apply List.ext_getElem <;> simp [arrayToBytes, toByte]

theorem toList_bytesOfList (l : List U8) : (bytesOfList l).toList = l.map toByte := by
  apply List.ext_getElem <;> simp [bytesOfList]

theorem toList_toByteVec (l : List U8) : (Model.toByteVec l).toList = l.map toByte := by
  apply List.ext_getElem <;> simp [Model.toByteVec, toByte]

/-- Byte vectors with the same bytes are heterogeneously equal. -/
theorem byteVec_heq {n m : ℕ} {v : ByteVec n} {w : ByteVec m} (h : v.toList = w.toList) :
    HEq v w := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst hnm
  exact heq_of_eq (Vector.toList_inj.mp h)

/-- Functions of byte vectors only depend on the bytes (not on how the length is written). -/
theorem byteVec_fun_congr {β : Sort _} (f : (n : ℕ) → ByteVec n → β) {n m : ℕ} {v : ByteVec n}
    {w : ByteVec m} (h : v.toList = w.toList) : f n v = f m w := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst hnm
  rw [Vector.toList_inj.mp h]

/-- Reading from a fresh SHAKE256 reader into the whole of an array. -/
theorem shake256Read_into_array {n : Usize} (a : Std.Array U8 n) (msg : List U8) :
    (Array.from_slice a (Model.shake256Read (msg, 0) (Array.to_slice a)).2).val.map toByte =
      (Wychelean.Hashes.SHA3.shake256 (Model.toByteVec msg) n.val).toList := by
  simp only [Model.shake256Read]
  rw [Array.from_slice_val _ _ (by simp)]
  simp only [Slice.from_val, List.drop_zero, List.map_map]
  have key : ∀ k, k = n.val → ∀ i (h1 : i < k) (h2 : i < n.val),
      (Wychelean.Hashes.SHA3.shake256 (Model.toByteVec msg) k)[i] =
        (Wychelean.Hashes.SHA3.shake256 (Model.toByteVec msg) n.val)[i] := by
    rintro k rfl i h1 h2; rfl
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, Vector.getElem_toList]
    simp only [List.length_map, Vector.length_toList] at h1
    rw [← key _ (by simp) i h1 (by simpa using h2)]
    simp [toByte]

theorem toList_vector_append {α : Type _} {n m : ℕ} (a : Vector α n) (b : Vector α m) :
    (Vector.append a b).toList = a.toList ++ b.toList := by
  change (a ++ b).toList = _
  simp

theorem toList_slice {α : Type _} {n : ℕ} (v : Vector α n) (off len : ℕ) (h : off + len ≤ n) :
    (Wychelean.slice v off len h).toList = (v.toList.drop off).take len := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2; simp [Wychelean.slice]

theorem arrayToBytes_ofByteVec {n : Usize} (v : ByteVec n.val) :
    arrayToBytes (Model.ofByteVec v) = v := by
  apply Vector.toList_inj.mp
  rw [toList_arrayToBytes]
  apply List.ext_getElem <;> simp [Model.ofByteVec, toByte]


-- INTERFACE
@[step] theorem G_spec (x y : Slice U8) :
    crypto.G x y
      ⦃ (a b : Std.Array U8 32#usize) => (arrayToBytes a, arrayToBytes b) = G (bytesOfList (x.val ++ y.val)) ⦄ := by
  simp only [crypto.G, digest.digest.Sha3_512_Digest.new_Sha3_512Sha3_512,
    digest.digest.Sha3_512_Digest.update_Sha3_512_RefSliceu8Sha3_512SharedSliceU8,
    digest.digest.Sha3_512_Digest.finalize_Sha3_512Sha3_512,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    hybrid_array.Array_u8_U32_DerefMut.deref_mut_u8_U32U8U32,
    hybrid_array.Array_u8_U64_Index_RangeTo_usize.index_u8_RangeTo_usize_U64U8RangeToUsizeU64,
    hybrid_array.Array_u8_U64_Index_RangeFrom_usize.index_u8_RangeFrom_usize_U64U8RangeFromUsizeU64,
    core.slice.SliceU8.copy_from_sliceU8, Array.to_slice_mut, bind_ok]
  set_option maxRecDepth 20000 in simp
  have hdv := arrayToBytes_ofByteVec (n := 64#usize)
    (Wychelean.Hashes.SHA3.sha3_512 (Model.toByteVec (x.val ++ y.val)))
  generalize hd : Model.ofByteVec (n := 64#usize) _ = d at hdv ⊢
  have hdl : d.val.map toByte = (Wychelean.Hashes.SHA3.sha3_512 (bytesOfList (x.val ++ y.val))).toList := by
    rw [← toList_arrayToBytes, hdv]; rfl
  have hlen : d.val.length = 64 := d.property
  step*
  have h1 : s1.val.length = 32 := by rw [s1_post]; simp [Array.to_slice, hlen]
  simp only [h1, ↓reduceIte, bind_ok]
  step*
  have h4 : s4.val.length = 32 := by rw [s4_post]; simp [Array.to_slice, hlen, List.slice]
  simp only [h4, ↓reduceIte, bind_ok, WP.spec_ok]
  simp only [WP.uncurry']
  refine Prod.ext ?_ ?_
  · simp only [G, Wychelean.split]
    apply Vector.toList_inj.mp
    rw [toList_arrayToBytes, Array.from_slice_val _ _ (by simpa using h1), s1_post]
    refine Eq.trans ?_ (toList_slice _ _ _ _).symm
    simp [Array.to_slice, List.map_take, hdl]
  · simp only [G, Wychelean.split]
    apply Vector.toList_inj.mp
    rw [toList_arrayToBytes, Array.from_slice_val _ _ (by simpa using h4), s4_post]
    refine Eq.trans ?_ (toList_slice _ _ _ _).symm
    simp [Array.to_slice, List.slice, List.map_take, List.map_drop, hdl]

-- INTERFACE
@[step] theorem H_spec_800 (x : Std.Array U8 800#usize) :
    crypto.H_Array_u8_U800Array_u8_U800 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  simp only [crypto.H_Array_u8_U800Array_u8_U800, digest.digest.Sha3_256_Digest.new_Sha3_256Sha3_256,
    digest.digest.Sha3_256_Digest.update_Sha3_256_Array_u8_U800Sha3_256Array_u8_U800,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    digest.digest.Sha3_256_Digest.finalize_into_Sha3_256Sha3_256]
  simp only [bind_ok, WP.spec_ok]
  refine (arrayToBytes_ofByteVec (n := 32#usize) _).trans ?_
  exact byteVec_fun_congr (fun _ v => Wychelean.Hashes.SHA3.sha3_256 v)
    (by simp [toList_arrayToBytes, toList_toByteVec])

-- INTERFACE
@[step] theorem H_spec_1184 (x : Std.Array U8 1184#usize) :
    crypto.H_Array_u8_U1184Array_u8_U1184 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  simp only [crypto.H_Array_u8_U1184Array_u8_U1184, digest.digest.Sha3_256_Digest.new_Sha3_256Sha3_256,
    digest.digest.Sha3_256_Digest.update_Sha3_256_Array_u8_U1184Sha3_256Array_u8_U1184,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    digest.digest.Sha3_256_Digest.finalize_into_Sha3_256Sha3_256]
  simp only [bind_ok, WP.spec_ok]
  refine (arrayToBytes_ofByteVec (n := 32#usize) _).trans ?_
  exact byteVec_fun_congr (fun _ v => Wychelean.Hashes.SHA3.sha3_256 v)
    (by simp [toList_arrayToBytes, toList_toByteVec])

-- INTERFACE
@[step] theorem H_spec_1568 (x : Std.Array U8 1568#usize) :
    crypto.H_Array_u8_U1568Array_u8_U1568 x
      ⦃ r => arrayToBytes r = H (arrayToBytes x) ⦄ := by
  simp only [crypto.H_Array_u8_U1568Array_u8_U1568, digest.digest.Sha3_256_Digest.new_Sha3_256Sha3_256,
    digest.digest.Sha3_256_Digest.update_Sha3_256_Array_u8_U1568Sha3_256Array_u8_U1568,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    digest.digest.Sha3_256_Digest.finalize_into_Sha3_256Sha3_256]
  simp only [bind_ok, WP.spec_ok]
  refine (arrayToBytes_ofByteVec (n := 32#usize) _).trans ?_
  exact byteVec_fun_congr (fun _ v => Wychelean.Hashes.SHA3.sha3_256 v)
    (by simp [toList_arrayToBytes, toList_toByteVec])

-- INTERFACE
@[step] theorem J_spec (x y : Slice U8) :
    crypto.J x y
      ⦃ r => arrayToBytes r = J (bytesOfList (x.val ++ y.val)) ⦄ := by
  simp only [crypto.J, shake.Shake_136_Default.default_136136, shake.Shake_136_Update.update_136136,
    shake.Shake_136_ExtendableOutput.finalize_xof_136136,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    hybrid_array.Array_u8_U32_DerefMut.deref_mut_u8_U32U8U32,
    shake.ShakeReader_136_XofReader.read_136136, Model.shake256Read, Array.to_slice_mut]
  simp [WP.spec_ok]
  apply Vector.toList_inj.mp
  rw [toList_arrayToBytes, Array.from_slice_val _ _ (by simp [Array.to_slice])]
  simp [Array.to_slice, List.map_map, Function.comp_def, toByte, J, Slice.from_val]
  rfl

-- INTERFACE
@[step] theorem PRF_spec_2 (s : Std.Array U8 32#usize) (b : U8) :
    crypto.PRF_U2U2 s b
      ⦃ r => arrayToBytes r = PRF η₂ (arrayToBytes s) (toByte b) ⦄ := by
  simp only [crypto.PRF_U2U2, shake.Shake_136_Default.default_136136, shake.Shake_136_Update.update_136136,
    shake.Shake_136_ExtendableOutput.finalize_xof_136136,
    hybrid_array.Array_u8_U32_AsRef_Sliceu8.as_ref_u8_U32U8U32,
    hybrid_array.Array_u8_U128_Default.default_u8_U128U8U128,
    hybrid_array.Array_u8_U128_DerefMut.deref_mut_u8_U128U8U128,
    shake.ShakeReader_136_XofReader.read_136136, Array.to_slice_mut]
  simp only [bind_ok, lift]
  set_option maxRecDepth 20000 in simp
  generalize hr : Model.shake256Read _ _ = p
  obtain ⟨_, s4⟩ := p
  simp [WP.spec_ok]
  apply Vector.toList_inj.mp
  rw [toList_arrayToBytes]
  have h4 := congrArg Prod.snd hr
  simp only at h4
  rw [← h4, shake256Read_into_array]
  exact byteVec_fun_congr (fun _ v => (Wychelean.Hashes.SHA3.shake256 v 128).toList)
    (by simp [toList_toByteVec, toList_vector_append]; exact (toList_arrayToBytes s).symm)

-- INTERFACE
@[step] theorem PRF_spec_3 (s : Std.Array U8 32#usize) (b : U8) :
    crypto.PRF_U3U3 s b
      ⦃ r => arrayToBytes r = PRF (η₁ .ML_KEM_512) (arrayToBytes s) (toByte b) ⦄ := by
  simp only [crypto.PRF_U3U3, shake.Shake_136_Default.default_136136, shake.Shake_136_Update.update_136136,
    shake.Shake_136_ExtendableOutput.finalize_xof_136136,
    hybrid_array.Array_u8_U32_AsRef_Sliceu8.as_ref_u8_U32U8U32,
    hybrid_array.Array_u8_U192_Default.default_u8_U192U8U192,
    hybrid_array.Array_u8_U192_DerefMut.deref_mut_u8_U192U8U192,
    shake.ShakeReader_136_XofReader.read_136136, Array.to_slice_mut]
  simp only [bind_ok, lift]
  set_option maxRecDepth 20000 in simp
  generalize hr : Model.shake256Read _ _ = p
  obtain ⟨_, s4⟩ := p
  simp [WP.spec_ok]
  apply Vector.toList_inj.mp
  rw [toList_arrayToBytes]
  have h4 := congrArg Prod.snd hr
  simp only at h4
  rw [← h4, shake256Read_into_array]
  exact byteVec_fun_congr (fun _ v => (Wychelean.Hashes.SHA3.shake256 v 192).toList)
    (by simp [toList_toByteVec, toList_vector_append]; exact (toList_arrayToBytes s).symm)

-- INTERFACE
@[step] theorem XOF_spec (ρ : Std.Array U8 32#usize) (i j : U8) :
    crypto.XOF ρ i j
      ⦃ r => r = XOF.Finalize (XOF.Absorb XOF.Init (arrayToBytes ρ ++ #v[toByte i, toByte j])) ⦄ := by
  simp only [crypto.XOF, shake.Shake_168_Default.default_168168, shake.Shake_168_Update.update_168168,
    shake.Shake_168_ExtendableOutput.finalize_xof_168168, hybrid_array.Array_u8_U32_Deref.deref_u8_U32U8U32,
    lift, bind_ok, WP.spec_ok]
  rw [Wychelean.Hashes.SHA3.SHAKE128.absorb_append, XOF.Finalize, XOF.Absorb, XOF.Init]
  exact byteVec_fun_congr (fun _ v => Wychelean.Hashes.SHA3.SHAKE128.finalize
      (Wychelean.Hashes.SHA3.SHAKE128.absorb Wychelean.Hashes.SHA3.SHAKE128.init v))
    (by
      rw [Vector.toList_append, Vector.toList_append, toList_toByteVec, toList_toByteVec,
        toList_arrayToBytes]
      simp [Slice.from_val, Array.to_slice, Array.make])


end MlKem.Properties
