import MlKem.Properties.Defs
import Wychelean.KEM.MLKEM.Properties.Loops

/-! # Facts about the spec

Lemmas about the spec alone, which the proofs about the Rust code need: that decoding inverts
encoding, and loop-free forms of K-PKE.KeyGen and K-PKE.Encrypt, whose loops (over the rows and
columns of `Â`, and over the PRF counter `N`) the Rust code expresses differently.

The theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Wychelean Wychelean.Hashes
open Wychelean.KEM.MLKEM
open scoped Wychelean.Notations Wychelean.Utils.Linear

namespace MlKem.Properties

/-! ## Helpers -/

namespace SpecLemmas
theorem foldl_eq_of_invariant {α : Type*} {n : ℕ} (f : α → Fin n → α) (P : ℕ → α → Prop) (v : α)
    (a : α) (h0 : P 0 a) (step : ∀ (i : Fin n) (a : α), P i.val a → P (i.val + 1) (f a i))
    (hR : ∀ x, P n x → x = v) : Fin.foldl n f a = v :=
  hR _ (NTT.foldl_invariant f P a h0 step)

theorem foldl_induction {α : Type*} {n : ℕ} (f : α → Fin n → α) (P : ℕ → α → Prop) (R : α → Prop)
    (a : α) (h0 : P 0 a) (step : ∀ (i : Fin n) (a : α), P i.val a → P (i.val + 1) (f a i))
    (hR : ∀ x, P n x → R x) : R (Fin.foldl n f a) :=
  hR _ (NTT.foldl_invariant f P a h0 step)

theorem range_size (n : ℕ) : [:n].size = n := by
  simp only [Std.Legacy.Range.size]; omega

theorem getElem_mat_set {α : Type*} {k l : ℕ} (M : Utils.Linear.Mat α k l) (i j : ℕ) (x : α)
    (i' j' : ℕ) (hi' : i' < k) (hj' : j' < l) :
    (Utils.Linear.Mat.set M i j x)[i'][j'] = if i' = i ∧ j' = j then x else M[i'][j'] := by
  by_cases hi : i < k <;>
    simp [Utils.Linear.Mat.set, hi, Vector.getElem_set] <;> grind

theorem sample_loop {α : Type*} (n : ℕ) (g : ℕ × Vector α n → α) (N0 : ℕ) (v0 : Vector α n)
    (hg : ∀ N v, g (N, v) = g (N, v0)) :
    List.foldl (fun p (x : {a // a ∈ List.range' 0 [:n].size}) =>
      (p.1 + 1, p.2.set x.1 (g p) (by obtain ⟨i, hi, e⟩ := List.mem_range'.1 x.2; have := range_size n; omega)))
      (N0, v0) (List.range' 0 [:n].size).attach = (N0 + n, Vector.ofFn fun i : Fin n => g (N0 + i, v0)) := by
  rw [foldl_attach_range' (n' := n) (hn := range_size n)]
  refine foldl_eq_of_invariant _ (fun t (st : ℕ × Vector α n) => st.1 = N0 + t ∧
      ∀ i (h : i < n), i < t → st.2[i] = g (N0 + i, v0)) _ _ ⟨rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · rintro t ⟨N, v⟩ ⟨hN, hv⟩
    dsimp only at hN hv ⊢
    refine ⟨by omega, fun i h hi => ?_⟩
    rw [Vector.getElem_set]
    split
    · subst_vars; simp [hg]
    · exact hv i h (by simp at *; omega)
  · rintro ⟨N, v⟩ ⟨hN, hv⟩
    dsimp only at hN hv
    subst hN
    congr 1
    ext i h
    rw [hv i h h, Vector.getElem_ofFn]

theorem mat_loop {α : Type*} (n : ℕ) (g : ℕ → ℕ → α) (M0 : Utils.Linear.Mat α n n) :
    List.foldl (fun b a => List.foldl (fun b a_1 => Utils.Linear.Mat.set b a a_1 (g a a_1)) b
      (List.range' 0 [:n].size)) M0 (List.range' 0 [:n].size) =
      Vector.ofFn fun i : Fin n => Vector.ofFn fun j : Fin n => g i j := by
  simp only [range_size, foldl_range'_eq, zero_add, one_mul]
  refine foldl_eq_of_invariant _ (fun t (M : Utils.Linear.Mat α n n) =>
      ∀ i (hi : i < n) j (hj : j < n), M[i][j] = if i < t then g i j else M0[i][j]) _ _
      (fun _ _ _ _ => by simp) ?_ ?_
  · intro i M hM
    refine foldl_induction _ (fun s (M' : Utils.Linear.Mat α n n) =>
      ∀ i' (hi : i' < n) j (hj : j < n), M'[i'][j] = if i' = i.val ∧ j < s then g i' j else M[i'][j])
      (fun M' => ∀ i' (hi : i' < n) j (hj : j < n), M'[i'][j] = if i' < i.val + 1 then g i' j else M0[i'][j])
      _ (fun _ _ _ _ => by simp) ?_ ?_
    · intro s M' hM' i' hi' j hj
      rw [getElem_mat_set _ _ _ _ _ _ hi' hj, hM' i' hi' j hj]
      grind
    · intro M' hM' i' hi' j hj
      rw [hM' i' hi' j hj, hM i' hi' j hj]
      grind
  · intro M hM
    ext i hi j hj
    rw [hM i hi j hj, if_pos hi]
    simp

/-- `∑_{j<d} bit_j(x) 2^j = x` for `x < 2^d`. -/
theorem sum_testBit (d x : ℕ) (hx : x < 2 ^ d) :
    ∑ j : Fin d, (x.testBit j).toNat * 2 ^ j.val = x := by
  induction d generalizing x with
  | zero => simp at hx; simp [hx]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_succ, pow_succ, pow_zero]
    have h := ih (x / 2) (by rw [pow_succ] at hx; omega)
    have : ∑ j : Fin d, (Nat.testBit (x / 2) j).toNat * (2 ^ j.val * 2) =
        2 * ∑ j : Fin d, (Nat.testBit (x / 2) j).toNat * 2 ^ j.val := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    rw [this, h, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h2 | h2 <;> simp [h2] <;> omega

theorem Bool_ofNat_mod_two (x : ℕ) : Bool.ofNat (x % 2) = x.testBit 0 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, Bool.ofNat]

/-- Algorithm 5 writes bit `j` of `F[i]` to position `i * d + j`. -/
theorem ByteEncode_eq (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 12) (F : Vector (ZMod (m d)) 256) :
    ByteEncode d F hd = bitsToBytes ((Vector.ofFn fun t : Fin (256 * d) =>
      (F[t.val / d]'(Nat.div_lt_of_lt_mul (by have := t.isLt; omega))).val.testBit (t.val % d)).cast
        (by omega)) := by
  unfold ByteEncode
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', bind_pure_comp,
    List.forIn'_pure_yield_eq_foldl, Id.run_pure, map_pure]
  congr 2
  rw [foldl_attach_range' (n' := 256)]
  swap; · rfl
  simp only [zero_add, one_mul]
  conv => enter [1, 2, b, i]; rw [foldl_attach_range' (n' := d) (hn := by simp only [Std.Legacy.Range.size]; omega)]
  refine foldl_eq_of_invariant _ (fun t (b : Vector Bool (256 * d)) => ∀ idx (h : idx < 256 * d),
      b[idx] = if idx < t * d then (F[idx / d]'(Nat.div_lt_of_lt_mul (by omega))).val.testBit (idx % d)
        else false)
    _ _ ?_ ?_ ?_
  · intro idx h; simp; rfl
  · intro i b hb
    refine foldl_induction _ (fun j (st : MProd ℕ (Vector Bool (256 * d))) =>
      st.1 = F[i.val].val / 2 ^ j ∧ ∀ idx (h : idx < 256 * d),
        st.2[idx] = if i.val * d ≤ idx ∧ idx < i.val * d + j then F[i.val].val.testBit (idx - i.val * d)
          else b[idx])
      (fun (st : MProd ℕ (Vector Bool (256 * d))) => ∀ idx (h : idx < 256 * d),
        st.2[idx] = if idx < (i.val + 1) * d then
          (F[idx / d]'(Nat.div_lt_of_lt_mul (by omega))).val.testBit (idx % d) else false)
      _ ?_ ?_ ?_
    · refine ⟨by simp, fun idx h => ?_⟩
      simp
    · rintro j ⟨a, b'⟩ ⟨ha, hb'⟩
      dsimp only at ha hb' ⊢
      subst ha
      have hbit : Bool.ofNat (F[i.val].val / 2 ^ j.val % 2) = F[i.val].val.testBit j.val := by
        rw [Bool_ofNat_mod_two, Nat.testBit_div_two_pow, Nat.zero_add]
      simp only [Nat.zero_add, Nat.one_mul, hbit]
      refine ⟨?_, fun idx h => ?_⟩
      · rw [Vector.getElem_set_self, ← hbit]
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        generalize F[i.val].val / 2 ^ j.val = x
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, Bool.ofNat]; omega
      · rw [Vector.getElem_set]
        split
        · rw [if_pos (by omega)]; congr 1; omega
        · rw [hb' idx h]
          congr 1
          apply propext
          omega
    · rintro ⟨a, b'⟩ ⟨_, hb'⟩ idx h
      dsimp only at hb' ⊢
      rw [hb' idx h, hb idx h]
      have e : (i.val + 1) * d = i.val * d + d := Nat.succ_mul _ _
      by_cases h1 : i.val * d ≤ idx ∧ idx < i.val * d + d
      · have hdiv : idx / d = i.val := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [if_pos h1, if_pos (by omega)]
        simp only [hdiv, Nat.mod_eq_sub_mul_div, Nat.mul_comm d]
      · rw [if_neg h1]
        by_cases h2 : idx < i.val * d
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
  · intro x hx
    ext idx h
    rw [hx idx h, if_pos (by omega)]
    simp

theorem idx_lt {i j d : ℕ} (hi : i < 256) (hj : j < d) : i * d + j < 8 * (32 * d) := by
  have := Bounds.idx_mul_add_lt i d j 256 hi hj
  omega

/-- Algorithm 6 reads `F[i]` from bits `i * d, …, i * d + d - 1`. -/
theorem ByteDecode_eq (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 12) (B : ByteVec (32 * d)) :
    ByteDecode B hd = Vector.ofFn fun i : Fin 256 =>
      ∑ j : Fin d, (((bytesToBits B)[i.val * d + j.val]'(idx_lt i.isLt j.isLt)).toNat : ZMod (m d)) *
        2 ^ j.val := by
  unfold ByteDecode
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', bind_pure_comp,
    List.forIn'_pure_yield_eq_foldl, map_pure]
  rw [foldl_attach_range' (n' := 256)]
  swap; · rfl
  simp only [zero_add, one_mul]
  refine foldl_eq_of_invariant _ (fun t (F : Vector (ZMod (m d)) 256) => ∀ i (h : i < 256), i < t →
    F[i] = ∑ j : Fin d, (((bytesToBits B)[i * d + j.val]'(idx_lt h j.isLt)).toNat : ZMod (m d)) *
      2 ^ j.val) _ _ ?_ ?_ ?_
  · intro i _ h; omega
  · intro i F hF i' h256 h'
    rw [Vector.getElem_set]
    split
    · subst_vars; rfl
    · exact hF i' h256 (by omega)
  · intro F hF
    ext i h
    rw [hF i h h, Vector.getElem_ofFn]

theorem m_le (d : ℕ) (hd : d ≤ 12) : m d ≤ 2 ^ d := by
  unfold m; split
  · exact le_rfl
  · obtain rfl : d = 12 := by omega
    decide

instance m_neZero (d : ℕ) : NeZero (m d) := ⟨by unfold m; split <;> positivity⟩

/-- `split` inverts `‖`. -/
theorem split_append {α : Type*} {a b : ℕ} (x : Vector α a) (y : Vector α b) (h : a + b = a + b) :
    split (x ‖ y) a b h = (x, y) := by
  ext i hi
  · simp [split, slice, Vector.append]
  · simp [split, slice, Vector.append]

end SpecLemmas

/-! ## Decoding inverts encoding -/

-- INTERFACE
theorem ByteDecode_ByteEncode (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 12) (F : Vector (ZMod (m d)) 256) :
    ByteDecode (d := d) (ByteEncode d F hd) hd = F := by
  rw [SpecLemmas.ByteDecode_eq, SpecLemmas.ByteEncode_eq, bytesToBits_bitsToBytes]
  ext i h
  simp only [Vector.getElem_ofFn, Vector.getElem_cast]
  have e1 (j : Fin d) : (i * d + j.val) / d = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have e2 (j : Fin d) : (i * d + j.val) % d = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  simp only [e1, e2]
  have hlt : F[i].val < 2 ^ d := lt_of_lt_of_le (ZMod.val_lt _) (SpecLemmas.m_le d hd.2)
  conv_rhs => rw [← ZMod.natCast_zmod_val F[i], ← SpecLemmas.sum_testBit d F[i].val hlt]
  push_cast
  rfl

-- INTERFACE
theorem ByteDecode₁₂_ByteEncode₁₂ {k : K} (v : NTTVector k) : ByteDecode₁₂ (ByteEncode₁₂ v) = v := by
  apply Vector.ext
  intro i hi
  simp only [ByteDecode₁₂, ByteEncode₁₂, Vector.getElem_ofFn]
  have : slice ((v.map fun f => ByteEncode 12 f.coeffs).flatten.cast (Nat.mul_comm _ _)) (32 * 12 * i)
      (32 * 12) (by have := Bounds.poly_vec_decode_idx_le 12 i hi; omega) = ByteEncode 12 v[i].coeffs := by
    ext t ht
    simp only [slice, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_flatten, Vector.getElem_map]
    have e1 : (32 * 12 * i + t) / (32 * 12) = i := by omega
    have e2 : (32 * 12 * i + t) % (32 * 12) = t := by omega
    simp only [e1, e2]
  simp only [this, ByteDecode_ByteEncode]

-- INTERFACE
theorem unpack_pack_ekPKE (p : ParameterSet) (e : EkPKE p) : (unpack (pack e) : EkPKE p) = e := by
  show (let (t, ρ) := split (ByteEncode₁₂ e.«t̂» ‖ e.ρ) (vecLen p) seedLen
    (⟨ByteDecode₁₂ t, ρ⟩ : EkPKE p)) = e
  rw [SpecLemmas.split_append]
  dsimp only
  rw [ByteDecode₁₂_ByteEncode₁₂]

-- INTERFACE
theorem unpack_pack_dk (p : ParameterSet) (d : Dk p) : (unpack (pack d) : Dk p) = d := by
  show (let (b, z) := split (pack d.pke ‖ d.ek ‖ d.h ‖ d.z) (dkPKELen p + ekLen p + hashLen) seedLen
    let (b, h) := split b (dkPKELen p + ekLen p) hashLen
    let (pke, ek) := split b (dkPKELen p) (ekLen p)
    (⟨unpack pke, ek, h, z⟩ : Dk p)) = d
  rw [SpecLemmas.split_append]
  dsimp only
  rw [SpecLemmas.split_append]
  dsimp only
  rw [SpecLemmas.split_append]
  dsimp only
  show (⟨⟨ByteDecode₁₂ (ByteEncode₁₂ d.pke.«ŝ»)⟩, d.ek, d.h, d.z⟩ : Dk p) = d
  rw [ByteDecode₁₂_ByteEncode₁₂]

/-! ## The hash functions don't depend on how the length of their input is written -/

-- INTERFACE
theorem G_cast {n n' : ℕ} (s : ByteVec n) (h : n = n') : G (s.cast h) = G s := by
  subst h; rfl

-- INTERFACE
theorem H_cast {n n' : ℕ} (s : ByteVec n) (h : n = n') : H (s.cast h) = H s := by
  subst h; rfl

-- INTERFACE
theorem J_cast {n n' : ℕ} (s : ByteVec n) (h : n = n') : J (s.cast h) = J s := by
  subst h; rfl

/-! ## Loop-free forms of K-PKE -/

-- INTERFACE
theorem K_PKE.KeyGen_eq (p : ParameterSet) (d : Seed) :
    K_PKE.KeyGen p d =
      let (ρ, σ) := G (d ‖ #v[UInt8.ofNat (k p)])
      let ŝ := PolyVector.NTT (Vector.ofFn fun i : Fin (k p) =>
        SamplePolyCBD (η := η₁ p) (PRF (η₁ p) σ (UInt8.ofNat i)))
      let ê := PolyVector.NTT (Vector.ofFn fun i : Fin (k p) =>
        SamplePolyCBD (η := η₁ p) (PRF (η₁ p) σ (UInt8.ofNat (k p + i))))
      (⟨Utils.Linear.Mat.mulVec (sampleMatrix (k p) ρ) ŝ + ê, ρ⟩, ⟨ŝ⟩) := by
  unfold K_PKE.KeyGen
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    List.forIn'_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl, Id.run_pure, map_pure, foldl_mprod_prod]
  rw [SpecLemmas.mat_loop]
  rw [SpecLemmas.sample_loop _ _ _ _ (fun _ _ => rfl), SpecLemmas.sample_loop _ _ _ _ (fun _ _ => rfl)]
  dsimp only
  simp only [Nat.zero_add]
  rfl

-- INTERFACE
theorem K_PKE.Encrypt_eq (p : ParameterSet) (ek : EkPKE p) (msg r : Seed) :
    K_PKE.Encrypt p ek msg r =
      let ŷ := PolyVector.NTT (Vector.ofFn fun i : Fin (k p) =>
        SamplePolyCBD (η := η₁ p) (PRF (η₁ p) r (UInt8.ofNat i)))
      let e₁ := Vector.ofFn fun i : Fin (k p) =>
        SamplePolyCBD (η := η₂) (PRF η₂ r (UInt8.ofNat (k p + i)))
      let e₂ := SamplePolyCBD (η := η₂) (PRF η₂ r (UInt8.ofNat (2 * k p)))
      let u := NTTVector.NTTInv
        (Utils.Linear.Mat.mulVec (Utils.Linear.Mat.transpose (sampleMatrix (k p) ek.ρ)) ŷ) + e₁
      let μ := Polynomial.Decompress 1 ⟨ByteDecode (msg.cast (by grind))⟩
      let v := Tq.NTTInv (Utils.Linear.innerProduct ek.«t̂» ŷ) + e₂ + μ
      ⟨PolyVector.Compress (dᵤ p) u, Polynomial.Compress (dᵥ p) v⟩ := by
  obtain ⟨t, ρ⟩ := ek
  unfold K_PKE.Encrypt
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    List.forIn'_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl, Id.run_pure, map_pure, foldl_mprod_prod]
  rw [SpecLemmas.mat_loop]
  rw [SpecLemmas.sample_loop _ _ _ _ (fun _ _ => rfl), SpecLemmas.sample_loop _ _ _ _ (fun _ _ => rfl)]
  dsimp only
  simp only [Nat.zero_add, two_mul]
  rfl

end MlKem.Properties
