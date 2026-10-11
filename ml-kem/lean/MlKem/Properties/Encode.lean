import MlKem.Properties.Arith

/-! # Byte encoding

Specs of `byte_encode` and `byte_decode` (Algorithms 5 and 6), and of the `Encode` impls built on
them.

The `@[step]` theorems marked `-- INTERFACE` are used by the rest of the proof; don't change their
statements. -/

open Aeneas Aeneas.Std Result
open Wychelean (ByteVec)
open Wychelean.KEM.MLKEM
open RustMlKem

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace MlKem.Properties

/-! # Helper lemmas

Both sides are characterized bit by bit. On the spec side, bit `t` of byte `k` of `ByteEncode_d(F)`
is bit `(8k + t) % d` of `F[(8k + t) / d]` (`ByteEncode_getLsbD`), and `ByteDecode_d(B)[i]` is the
number whose bits are the bits `i·d, …, i·d + d - 1` of `B` (`byteDecode_getElem`). On the Rust
side, the chunked `u128` packing is a regrouping of the same bit string: `chunkBit_step`,
`enc_chunk_step`, `unpack_bits` and `dec_chunk_step` do the arithmetic once, generically in `D`,
with `D · ValueStep = 8 · ByteStep` as a hypothesis. The per-`D` loop specs below only run the
extracted code symbolically and call these lemmas. -/

/-! ## Generic lemmas: `Id.run` loops of the spec -/

theorem forIn'_list_inv {β : Type} (P : ℕ → β → Prop) :
    ∀ (k s : ℕ) (init : β) (f : (a : ℕ) → a ∈ List.range' s k → β → Id (ForInStep β)),
    P s init →
    (∀ i hi b, P i b → ∃ b', f i hi b = ForInStep.yield b' ∧ P (i+1) b') →
    P (s + k) (Id.run (forIn' (List.range' s k) init f)) := by
  intro k
  induction k with
  | zero => intro s init f h0 _; simpa using h0
  | succ k ih =>
    intro s init f h0 hstep
    obtain ⟨b', hb', hP⟩ := hstep s (by simp) init h0
    have := ih (s+1) b' (fun a h b => f a (List.mem_cons_of_mem _ h) b) hP
      (fun i hi b hb => hstep i _ b hb)
    rw [show s + (k+1) = s + 1 + k by omega]
    simp only [List.range'_succ, List.forIn'_cons, Id.run, Bind.bind, hb'] at this ⊢
    exact this

theorem forIn'_range_inv {β : Type} (n : ℕ) (init : β) (f : (a : ℕ) → a ∈ [:n] → β → Id (ForInStep β))
    (P : ℕ → β → Prop) (h0 : P 0 init)
    (hstep : ∀ i hi b, P i b → ∃ b', f i hi b = ForInStep.yield b' ∧ P (i+1) b') :
    P n (Id.run (forIn' [:n] init f)) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have := forIn'_list_inv P n 0 init
    (fun a h b => f a (Std.Legacy.Range.mem_of_mem_range' (by simpa using h)) b) h0
    (fun i hi b hb => hstep i _ b hb)
  simp only [Nat.zero_add] at this; exact this

/-! ## The spec, bit by bit -/

theorem idx_lt' {i d j : ℕ} (hi : i < 256) (hj : j < d) : i * d + j < 256 * d :=
  Bounds.idx_mul_add_lt i d j 256 hi hj

theorem div_lt_of_lt_mul' {p d : ℕ} (h : p < 256 * d) : p / d < 256 := by
  apply Nat.div_lt_of_lt_mul; rwa [Nat.mul_comm]

theorem div_pow_sub_testBit (x j : ℕ) : (x / 2 ^ j - (x.testBit j).toNat) / 2 = x / 2 ^ (j + 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ j = a
  rcases Nat.mod_two_eq_zero_or_one a with h2 | h2 <;> simp [h2]; omega

/-- Invariant of the outer loop of `ByteEncode`. -/
def EncInv (d : ℕ) (F : Vector (ZMod (m d)) 256) (i : ℕ) (b : Vector Bool (256 * d)) : Prop :=
  ∀ i' (hi' : i' < 256) j (hj : j < d), i' < i → b[i' * d + j]'(idx_lt' hi' hj) = F[i'].val.testBit j

/-- Invariant of the inner loop of `ByteEncode`. -/
def EncInvIn (d : ℕ) (F : Vector (ZMod (m d)) 256) (i : ℕ) (j : ℕ) (r : MProd ℕ (Vector Bool (256 * d))) : Prop :=
  ∀ (hi : i < 256), r.fst = F[i].val / 2 ^ j ∧
  ∀ i' (hi' : i' < 256) j' (hj : j' < d), (i' < i ∨ (i' = i ∧ j' < j)) →
    r.snd[i' * d + j']'(idx_lt' hi' hj) = F[i'].val.testBit j'

theorem byteEncode_bits_of (d : ℕ) (F : Vector (ZMod (m d)) 256) (b : Vector Bool (256 * d))
    (hb : EncInv d F 256 b) (h : 256 * d = 8 * (32 * d)) (k : ℕ) (hk : k < 32 * d) (t : ℕ) (ht : t < 8) :
    (Wychelean.bitsToBytes (b.cast h))[k].toBitVec.getLsbD t =
      (F[(8*k+t)/d]'(div_lt_of_lt_mul' (by omega))).val.testBit ((8*k+t)%d) := by
  rw [Wychelean.bitsToBytes_getLsbD _ _ hk _ ht, Vector.getElem_cast]
  have hd : 0 < d := by rcases Nat.eq_zero_or_pos d with h | h <;> [simp [h] at hk; exact h]
  have h1 : (8*k+t)/d < 256 := div_lt_of_lt_mul' (by omega)
  have := hb ((8*k+t)/d) h1 ((8*k+t)%d) (Nat.mod_lt _ hd) h1
  simp only [Nat.div_add_mod'] at this
  exact this

theorem encInv_succ (d : ℕ) (F : Vector (ZMod (m d)) 256) (i : ℕ) (hi : i < 256)
    (r : MProd ℕ (Vector Bool (256 * d))) (h : EncInvIn d F i d r) : EncInv d F (i + 1) r.snd := by
  intro i' hi' j hj hlt
  exact (h hi).2 i' hi' j hj (by omega)

/-- Bit `t` of byte `k` of `ByteEncode_d(F)` is bit `(8k + t) mod d` of `F[(8k + t) / d]`. -/
theorem ByteEncode_getLsbD (d : ℕ) (F : Vector (ZMod (m d)) 256) (h : 1 ≤ d ∧ d ≤ 12) (k : ℕ)
    (hk : k < 32 * d) (t : ℕ) (ht : t < 8) :
    (ByteEncode d F h)[k].toBitVec.getLsbD t =
      (F[(8*k+t)/d]'(div_lt_of_lt_mul' (by omega))).val.testBit ((8*k+t)%d) := by
  unfold ByteEncode
  simp only [Id.run_bind, Id.run_pure]
  refine byteEncode_bits_of d F _ ?_ _ k hk t ht
  apply forIn'_range_inv (P := EncInv d F)
  · intro i' hi' j hj h; omega
  · intro i hi b hb
    refine ⟨_, rfl, ?_⟩
    have hi256 : i < 256 := hi.2.1
    refine encInv_succ d F i hi256 _ ?_
    apply forIn'_range_inv (P := EncInvIn d F i)
    · intro _; refine ⟨by simp, ?_⟩
      intro i' hi' j' hj' hlt
      rcases hlt with hlt | hlt
      · exact hb i' hi' j' hj' hlt
      · omega
    · intro j hj r hr
      refine ⟨_, rfl, ?_⟩
      intro _
      obtain ⟨hr1, hr2⟩ := hr hi256
      have hbit : Bool.ofNat (r.fst % 2) = F[i].val.testBit j := by
        rw [hr1, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (F[i].val / 2 ^ j) with h2 | h2 <;> simp [h2, Bool.ofNat]
      refine ⟨?_, ?_⟩
      · simp only [Vector.getElem_set_self, hbit]
        rw [hr1, div_pow_sub_testBit]
      · intro i' hi' j' hj' hlt
        simp only
        rw [Vector.getElem_set]
        split
        · rename_i heq
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · have := Bounds.idx_mul_add_lt i' d j' i hlt hj'; omega
          · have : j = j' := by omega
            subst this; exact hbit
        · rename_i hne
          apply hr2 i' hi' j' hj'
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · exact Or.inl hlt
          · right; refine ⟨rfl, ?_⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h | h
            · exact h
            · subst h; exact absurd rfl hne

theorem sum_bits (d : ℕ) : ∀ (n : ℕ) (f : ℕ → Bool), n < 2 ^ d → (∀ j < d, n.testBit j = f j) →
    ∑ j : Fin d, (f j).toNat * 2 ^ j.val = n := by
  induction d with
  | zero => intro n f hn _; simp at hn; simp [hn]
  | succ d ih =>
    intro n f hn hf
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (n % 2 ^ d) f (Nat.mod_lt _ (by positivity))
      (fun j hj => by rw [Nat.testBit_mod_two_pow]; simp [hj, hf j (by omega)])]
    rw [← hf d (by omega), Nat.testBit_eq_decide_div_mod_eq]
    have h2 : n / 2 ^ d < 2 := by
      apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_succ]; exact hn
    have := Nat.mod_add_div n (2 ^ d)
    generalize n / 2 ^ d = a at *
    interval_cases a <;> simp <;> omega

/-- Invariant of the loop of `ByteDecode`. -/
def DecInv {d : ℕ} (B : ByteVec (32 * d)) (i : ℕ) (F : Vector (ZMod (m d)) 256) : Prop :=
  ∀ i' (hi' : i' < 256), i' < i →
    F[i'] = ∑ j : Fin d, (((Wychelean.bytesToBits B)[i' * d + j.val]'(by
      have := idx_lt' hi' j.isLt; omega)).toNat : ZMod (m d)) * 2 ^ j.val

/-- `ByteDecode_d(B)[i]` is the number whose `d` bits are the bits `i·d, …, i·d + d - 1` of `B`. -/
theorem byteDecode_getElem {d : ℕ} (B : ByteVec (32 * d)) (h : 1 ≤ d ∧ d ≤ 12) (i : ℕ) (hi : i < 256)
    (n : ℕ) (hn : n < 2 ^ d)
    (hbits : ∀ j (hj : j < d), n.testBit j =
      (B[(i * d + j) / 8]'(by have := idx_lt' hi hj; omega)).toBitVec.getLsbD ((i * d + j) % 8)) :
    (ByteDecode B h)[i] = (n : ZMod (m d)) := by
  have key : ∀ F : Vector (ZMod (m d)) 256, DecInv B 256 F → F[i] = (n : ZMod (m d)) := by
    intro F hF
    rw [hF i hi hi, ← sum_bits d n (fun j => if hj : j < d then
      (Wychelean.bytesToBits B)[i * d + j]'(by have := idx_lt' hi hj; omega) else false) hn ?_]
    · push_cast
      apply Finset.sum_congr rfl
      intro j _
      simp [j.isLt]
    · intro j hj
      simp [hj, hbits j hj, Wychelean.bytesToBits]
  unfold ByteDecode
  simp only [Id.run_bind, Id.run_pure]
  apply key
  apply forIn'_range_inv (P := DecInv B)
  · intro i' _ h; omega
  · intro i₀ hi₀ F hF
    refine ⟨_, rfl, ?_⟩
    intro i' hi' hlt
    rw [Vector.getElem_set]
    split
    · rename_i heq; subst heq; rfl
    · exact hF i' hi' (by omega)

/-! ## Generic lemmas: the Rust side -/

theorem range_next_some (r : core.ops.range.Range Usize) (h : r.start.val < r.end.val) :
    core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next r
    ⦃ (opt : Option Usize) (r' : core.ops.range.Range Usize) =>
      opt = some r.start ∧ r'.start.val = r.start.val + 1 ∧ r'.end = r.end ⦄ :=
  core.iter.range.IteratorRange.next_Usize_some_spec r h

theorem range_next_none (r : core.ops.range.Range Usize) (h : r.start.val ≥ r.end.val) :
    core.ops.range.RangeUsize.Insts.CoreIterTraitsIteratorIterator.next r
    ⦃ (opt : Option Usize) (r' : core.ops.range.Range Usize) => opt = none ∧ r' = r ⦄ :=
  core.iter.range.IteratorRange.next_Usize_none_spec r h

/-- The bits of a partially packed chunk: the first `n` values of `D` bits starting at `start`. -/
def chunkBit (D : ℕ) (vals : List U16) (start n q : ℕ) : Bool :=
  decide (q < D * n) && vals[start + q / D]!.val.testBit (q % D)

/-- Bit `p` of the concatenation of the `D`-bit values `vals`. -/
def encBit (D : ℕ) (vals : List U16) (p : ℕ) : Bool := vals[p / D]!.val.testBit (p % D)

theorem div_mod_of_range {D j q : ℕ} (h1 : D * j ≤ q) (h2 : q < D * (j + 1)) :
    q / D = j ∧ q % D = q - D * j := by
  have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h | h <;> [simp [h] at h2; exact h]
  have : q / D = j :=
    Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.mul_comm]; exact h2)
  refine ⟨this, ?_⟩
  have := Nat.div_add_mod q D
  rw [‹q / D = j›] at this
  omega

theorem chunkBit_step (D : ℕ) (vals : List U16) (start j : ℕ) (x v : ℕ)
    (hv : v = vals[start + j]!.val) (hvlt : v < 2 ^ D)
    (hx : ∀ q, x.testBit q = chunkBit D vals start j q) (hD : D * (j + 1) ≤ 128) :
    ∀ q, (x ||| (v <<< (D * j)) % 2 ^ 128).testBit q = chunkBit D vals start (j + 1) q := by
  intro q
  rw [Nat.testBit_or, hx, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  unfold chunkBit
  by_cases hq1 : q < D * j
  · have : q < D * (j + 1) := by rw [Nat.mul_succ]; omega
    simp [hq1, this, Nat.not_le.mpr hq1]
  · by_cases hq2 : q < D * (j + 1)
    · obtain ⟨hdiv, hmod⟩ := div_mod_of_range (Nat.le_of_not_lt hq1) hq2
      simp [hq1, hq2, hdiv, hmod, hv, Nat.le_of_not_lt hq1, show q < 128 by omega]
    · have hb : v.testBit (q - D * j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hvlt
          (Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_succ] at hq2; omega)))
      simp [hq1, hq2, hb]

theorem array_set_getElem! {α : Type} [Inhabited α] {n : Usize} (a : Std.Array α n) (p : Usize) (v : α) (K : ℕ) :
    (a.set p v).val[K]! = if K = p.val ∧ K < a.val.length then v else a.val[K]! := by
  simp only [Std.Array.set_val_eq, List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : p.val = K
  · subst h1; by_cases h2 : p.val < n.val <;> simp [h2]
  · simp [h1, Ne.symm h1]

theorem enc_inner_step (N BS c s : ℕ) (bytes r xb : List U8) (p : Usize) (v : U8) (n : Usize)
    (a : Std.Array U8 n) (ha : a.val = bytes) (hn : n.val = N)
    (hp : p.val = c * BS + s) (hs : s < BS) (hv : v = xb[s]!)
    (hr : ∀ K < N, r[K]! = if c * BS + (s + 1) ≤ K ∧ K < c * BS + BS then xb[K - c * BS]!
      else (a.set p v).val[K]!) :
    ∀ K < N, r[K]! = if c * BS + s ≤ K ∧ K < c * BS + BS then xb[K - c * BS]! else bytes[K]! := by
  intro K hK
  have hlen : bytes.length = N := by rw [← ha]; simp [hn]
  rw [hr K hK, array_set_getElem!, ha]
  by_cases hK1 : K = c * BS + s
  · subst hK1
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), hv]
    congr 1; omega
  · by_cases hK2 : c * BS + (s + 1) ≤ K ∧ K < c * BS + BS
    · rw [if_pos hK2, if_pos (by omega)]
    · rw [if_neg hK2, if_neg (by omega)]
      by_cases hK3 : c * BS + s ≤ K ∧ K < c * BS + BS
      · omega
      · rw [if_neg hK3]

/-- Bit `t` of byte `k` of `x.to_le_bytes()` is bit `8k + t` of `x`. -/
theorem toLEBytes_testBit (x : U128) (k t : ℕ) (hk : k < 16) (ht : t < 8) :
    ((x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8))[k]!).val.testBit t = x.val.testBit (8 * k + t) := by
  have hlen : k < (x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)).length := by simp; omega
  rw [getElem!_pos (x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)) k hlen, List.getElem_map]
  have := BitVec.toLEBytes_getElem_testBit x.bv k t (by simpa using hlen) ⟨ht, by omega⟩
  change Byte.testBit _ t = _
  rw [this, BitVec.getElem_eq_testBit_toNat]
  rfl

theorem enc_chunk_step (D VS BS N : ℕ) (hDVS : D * VS = 8 * BS) (hBS : BS ≤ 16)
    (vals : List U16) (c : ℕ) (x : U128)
    (hx : ∀ q, x.val.testBit q = chunkBit D vals (c * VS) VS q)
    (bytes bytes1 : List U8)
    (h1 : ∀ K < N, bytes1[K]! = if c * BS ≤ K ∧ K < c * BS + BS then
      (x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8))[K - c * BS]! else bytes[K]!)
    (hinv : ∀ K < c * BS, ∀ t < 8, bytes[K]!.val.testBit t = encBit D vals (8 * K + t))
    (hN : c * BS + BS ≤ N) :
    ∀ K < (c + 1) * BS, ∀ t < 8, bytes1[K]!.val.testBit t = encBit D vals (8 * K + t) := by
  intro K hK t ht
  rw [h1 K (by rw [Nat.succ_mul] at hK; omega)]
  split
  · rename_i hr
    obtain ⟨k, rfl⟩ : ∃ k, K = c * BS + k := ⟨K - c * BS, by omega⟩
    rw [show c * BS + k - c * BS = k by omega, toLEBytes_testBit x k t (by omega) ht, hx]
    unfold chunkBit encBit
    have h8 : 8 * k + t < D * VS := by omega
    have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h | h <;> [simp [h] at h8; exact h]
    have : 8 * (c * BS + k) + t = D * (c * VS) + (8 * k + t) := by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 8 c, Nat.mul_assoc, ← hDVS]; ring
    rw [this, Nat.mul_add_div hD, Nat.mul_add_mod]
    simp [h8]
  · rename_i hr
    exact hinv K (by rw [Nat.succ_mul] at hK; omega) t ht


/-! ## Glue between the Rust bits and the spec -/

theorem m_pos (D : ℕ) : 0 < m D := by unfold m; split <;> positivity

theorem m_le (D : ℕ) (hD : D ≤ 12) : m D ≤ 2 ^ D := by
  unfold m; split
  · exact le_refl _
  · have : D = 12 := by omega
    subst this; decide

theorem bounded_lt {D : ℕ} (hD : D ≤ 12) (a : Coeffs) (ha : a.Bounded (m D)) :
    ∀ i (hi : i < 256), a.val[i]!.val < 2 ^ D := by
  intro i hi
  have hl : i < a.val.length := by simp; omega
  rw [getElem!_pos a.val i hl]
  exact lt_of_lt_of_le (ha _ (List.getElem_mem hl)) (m_le D hD)

theorem toVector_val {D : ℕ} (a : Coeffs) (ha : a.Bounded (m D)) (i : ℕ) (hi : i < 256) :
    ((a.toVector (m D))[i]).val = a.val[i]!.val := by
  have : NeZero (m D) := ⟨(m_pos D).ne'⟩
  have hl : i < a.val.length := by simp; omega
  simp only [Coeffs.toVector, Vector.getElem_ofFn, toZMod, ZMod.val_natCast]
  rw [getElem!_pos a.val i hl]
  exact Nat.mod_eq_of_lt (ha _ (List.getElem_mem hl))

theorem encode_glue (D : ℕ) (hD : 1 ≤ D ∧ D ≤ 12) (a : Coeffs) (ha : a.Bounded (m D)) {N : Usize}
    (r : Std.Array U8 N) (hN : N.val = 32 * D)
    (hr : ∀ K < 32 * D, ∀ t < 8, r.val[K]!.val.testBit t = encBit D a.val (8 * K + t))
    (k : ℕ) (hk : k < 32 * D) :
    (arrayToBytes r)[k]'(by omega) = (ByteEncode D (a.toVector (m D)) hD)[k] := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [ByteEncode_getLsbD D _ hD k hk t ht, toVector_val a ha _ (div_lt_of_lt_mul' (by omega))]
  have hl : k < r.val.length := by simp; omega
  have := hr k hk t ht
  rw [getElem!_pos r.val k hl] at this
  simp only [arrayToBytes, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec]
  exact this

/-! ## Decoding: generic lemmas -/

theorem getElem_eq_getElem!' {α : Type} [Inhabited α] (l : List α) (i j : ℕ) (h : i < l.length)
    (hij : i = j) : l[i] = l[j]! := by
  subst hij; rw [getElem!_pos]

theorem unpack_step (BS s : ℕ) (xb : Std.Array U8 16#usize) (bytes r : List U8) (start : ℕ)
    (k : Usize) (hk : k.val = s) (v : U8) (hv : v = bytes[start + s]!) (hs : s < BS)
    (hr : ∀ k' < 16, r[k']! = if s + 1 ≤ k' ∧ k' < BS then bytes[start + k']! else (xb.set k v).val[k']!) :
    ∀ k' < 16, r[k']! = if s ≤ k' ∧ k' < BS then bytes[start + k']! else xb.val[k']! := by
  intro k' hk'
  rw [hr k' hk', array_set_getElem!]
  by_cases h1 : k' = s
  · subst h1
    rw [if_neg (by omega), if_pos (by simp; omega), if_pos (by omega), hv]
  · rw [if_neg (show ¬(k' = k.val ∧ k' < xb.val.length) by omega)]
    by_cases h2 : s + 1 ≤ k' ∧ k' < BS
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

theorem from_le_bytes_testBit (xb : Std.Array U8 16#usize) (q : ℕ) (hq : q < 128) :
    (core.num.U128.from_le_bytes xb).val.testBit q = xb.val[q / 8]!.val.testBit (q % 8) := by
  have h1 : (core.num.U128.from_le_bytes xb).val.testBit q = (core.num.U128.from_le_bytes xb).bv[q]! := by
    rw [BitVec.getElem!_eq_testBit_toNat]; rfl
  rw [h1]
  simp only [core.num.U128.from_le_bytes]
  erw [BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
  have hl : q / 8 < xb.val.length := by simp; omega
  rw [getElem!_pos (xb.val.map U8.bv) (q / 8) (by simpa using hl), getElem!_pos xb.val (q / 8) hl,
    List.getElem_map]
  rfl
  simp

theorem dec_val_lt12 (D : ℕ) (hD : D < 12) (y : ℕ) : (y % 2 ^ 16) &&& (2 ^ D - 1) = y % 2 ^ D % m D := by
  have : m D = 2 ^ D := by simp [m, hD]
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem dec_val_12 (y : ℕ) : ((y % 2 ^ 16) &&& (2 ^ 12 - 1)) % 3329 = y % 2 ^ 12 % m 12 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd y (show 2 ^ 12 ∣ 2 ^ 16 by norm_num)]; rfl

/-- The `D`-bit value `j` of the chunk `x`, reduced as `byte_decode` does. -/
def decVal (D x j : ℕ) : ℕ := (x >>> (D * j)) % 2 ^ D % m D

theorem dec_inner_step (D VS c s x : ℕ) (vals : Std.Array U16 256#usize) (r : List U16)
    (p : Usize) (v : U16) (hp : p.val = c * VS + s) (hs : s < VS) (hv : v.val = decVal D x s)
    (hr : ∀ i < 256, (c * VS + (s + 1) ≤ i → i < c * VS + VS → r[i]!.val = decVal D x (i - c * VS)) ∧
      (¬(c * VS + (s + 1) ≤ i ∧ i < c * VS + VS) → r[i]! = (vals.set p v).val[i]!)) :
    ∀ i < 256, (c * VS + s ≤ i → i < c * VS + VS → r[i]!.val = decVal D x (i - c * VS)) ∧
      (¬(c * VS + s ≤ i ∧ i < c * VS + VS) → r[i]! = vals.val[i]!) := by
  intro i hi
  obtain ⟨hr1, hr2⟩ := hr i hi
  rw [array_set_getElem!] at hr2
  by_cases hi1 : i = c * VS + s
  · subst hi1
    refine ⟨fun _ _ => ?_, fun h => by omega⟩
    rw [hr2 (by omega), if_pos (by simp; omega), hv]
    congr 1; omega
  · refine ⟨fun h1 h2 => hr1 (by omega) h2, fun h => ?_⟩
    rw [hr2 (by omega), if_neg (by omega)]

/-- `v` is the `i`-th value decoded from `bytes`. -/
def DecOK (D : ℕ) (bytes : List U8) (i : ℕ) (v : U16) : Prop :=
  ∃ n, n < 2 ^ D ∧ (∀ j < D, n.testBit j = bytes[(i * D + j) / 8]!.val.testBit ((i * D + j) % 8)) ∧
    v.val = n % m D


theorem repeat_getElem! {α : Type} [Inhabited α] (n : Usize) (x : α) (k : ℕ) (hk : k < n.val) :
    (Std.Array.repeat n x).val[k]! = x := by
  rw [Std.Array.repeat_val, getElem!_pos _ k (by simpa using hk), List.getElem_replicate]

theorem unpack_bits (BS : ℕ) (hBS : BS ≤ 16) (bytes : List U8) (start : ℕ) (xb : Std.Array U8 16#usize)
    (hxb : ∀ k < 16, xb.val[k]! = if 0 ≤ k ∧ k < BS then bytes[start + k]!
      else (Std.Array.repeat 16#usize 0#u8).val[k]!) :
    ∀ q, (core.num.U128.from_le_bytes xb).val.testBit q =
      (decide (q < 8 * BS) && bytes[start + q / 8]!.val.testBit (q % 8)) := by
  intro q
  by_cases hq : q < 128
  · rw [from_le_bytes_testBit xb q hq, hxb (q / 8) (by omega)]
    by_cases h8 : q < 8 * BS
    · rw [if_pos (by omega)]; simp [h8]
    · rw [if_neg (by omega), repeat_getElem! _ _ _ (by simp; omega)]; simp [h8]
  · have : q ≥ 8 * BS := by omega
    simp only [show decide (q < 8 * BS) = false by simp; omega, Bool.false_and]
    apply Nat.testBit_eq_false_of_lt
    calc _ < 2 ^ 128 := by scalar_tac
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)

theorem dec_chunk_step (D VS BS : ℕ) (hDVS : D * VS = 8 * BS) (hBS : BS ≤ 16)
    (bytes : List U8) (c x : ℕ)
    (hx : ∀ q, x.testBit q = (decide (q < 8 * BS) && bytes[c * BS + q / 8]!.val.testBit (q % 8)))
    (vals vals1 : List U16)
    (h1 : ∀ i < 256, (c * VS ≤ i → i < c * VS + VS → vals1[i]!.val = decVal D x (i - c * VS)) ∧
      (¬(c * VS ≤ i ∧ i < c * VS + VS) → vals1[i]! = vals[i]!))
    (hinv : ∀ i < c * VS, DecOK D bytes i vals[i]!) (hc : c * VS + VS ≤ 256) :
    ∀ i < (c + 1) * VS, DecOK D bytes i vals1[i]! := by
  intro i hi
  obtain ⟨h1a, h1b⟩ := h1 i (by rw [Nat.succ_mul] at hi; omega)
  by_cases hlo : c * VS ≤ i
  · obtain ⟨j, rfl⟩ : ∃ j, i = c * VS + j := ⟨i - c * VS, by omega⟩
    have hj : j < VS := by rw [Nat.succ_mul] at hi; omega
    refine ⟨(x >>> (D * j)) % 2 ^ D, Nat.mod_lt _ (by positivity), ?_, ?_⟩
    · intro j' hj'
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hx]
      have hlt : D * j + j' < 8 * BS := by
        rw [← hDVS]
        calc D * j + j' < D * j + D := by omega
          _ = D * (j + 1) := by ring
          _ ≤ D * VS := Nat.mul_le_mul_left _ hj
      have : (c * VS + j) * D + j' = 8 * (c * BS) + (D * j + j') := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm VS D, hDVS]; ring
      rw [this, Nat.mul_add_div (by norm_num), Nat.mul_add_mod]
      simp [hj', hlt]
    · rw [h1a (by omega) (by omega)]
      rw [show c * VS + j - c * VS = j by omega]; rfl
  · rw [h1b (by omega)]
    exact hinv i (by omega)

theorem arrayToBytes_getElem {n : Usize} (b : Std.Array U8 n) (k : ℕ) (hk : k < n.val) :
    (arrayToBytes b)[k] = UInt8.ofBitVec (b.val[k]!).bv := by
  simp only [arrayToBytes, Vector.getElem_ofFn]
  rw [getElem!_pos b.val k (by simpa using hk)]

theorem decode_glue (D : ℕ) (hD : 1 ≤ D ∧ D ≤ 12) (B : ByteVec (32 * D)) (b : List U8)
    (hB : ∀ k (hk : k < 32 * D), B[k] = UInt8.ofBitVec (b[k]!).bv) (r : Coeffs)
    (hr : ∀ i < 256, DecOK D b i r.val[i]!) :
    r.Bounded (m D) ∧ r.toVector (m D) = ByteDecode B hD := by
  have hlen : r.val.length = 256 := by simp
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨n, _, _, hv⟩ := hr i (by omega)
    rw [← getElem!_pos r.val i hi, hv]
    exact Nat.mod_lt _ (m_pos D)
  · apply Vector.ext
    intro i hi
    obtain ⟨n, hn, hbits, hv⟩ := hr i hi
    rw [byteDecode_getElem B hD i hi n hn ?_]
    · simp only [Coeffs.toVector, Vector.getElem_ofFn, toZMod]
      rw [← getElem!_pos r.val i (by omega), hv, ZMod.natCast_mod]
    · intro j hj
      rw [hbits j hj, hB _ (by have := idx_lt' hi hj; omega), UInt8.toBitVec_ofBitVec]
      rfl

@[step] theorem truncate_u128_spec (x : U128) :
    module_lattice.truncate.u16_Truncate_u128.truncate x ⦃ r => r.val = x.val % 2 ^ 16 ⦄ := by
  unfold module_lattice.truncate.u16_Truncate_u128.truncate
  simp only [lift, bind_ok, WP.spec_ok, UScalar.cast_val_eq, UScalar.val_and,
    core.convert.num.FromU128U16.from_val_eq, UScalarTy.U16_numBits_eq]
  have h2 : core.num.U16.MAX.val = 2 ^ 16 - 1 := by simp [core.num.U16.MAX]; rfl
  rw [h2, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

@[step] theorem bitand_u16_spec (x y : U16) :
    U16.Insts.CoreOpsBitBitAndU16.bitand x y ⦃ r => r.val = x.val &&& y.val ⦄ := by
  simp [U16.Insts.CoreOpsBitBitAndU16.bitand]


/-! ### Encoding, `D = 1` -/

theorem pack_chunk_1_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 8 ≤ 256) (hend : iter.end.val = 8) (hstart : iter.start.val ≤ 8)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 1)
    (hx : ∀ q, x.val.testBit q = chunkBit 1 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U1BaseFieldU1_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 1 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U1BaseFieldU1_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 1 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 8 := by omega
    rw [this] at hx; exact hx
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_1_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 8 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 1) :
    module_lattice.encoding.pack_chunk_BaseField_U1BaseFieldU1 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 1 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U1BaseFieldU1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_1_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_1_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 32#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 1) (hend : iter.end.val = 1) (hst : iter.start.val ≤ 1)
    (hc : c.val * 1 + 1 ≤ 32) :
    module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 32, r.val[K]! = if c.val * 1 + iter.start.val ≤ K ∧ K < c.val * 1 + 1 then
        xb.val[K - c.val * 1]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U32_IndexMut_usize.index_mut_u8_usize_U32U8UsizeU32]
    step*
    rw [index_mut_u8_usize_U32_back_post, h1] at r_post
    exact enc_inner_step 32 1 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 1 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_1_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 32#usize)
    (hvs : val_step.val = 8) (hbs : byte_step.val = 1) (hend : iter.end.val = 32)
    (hst : iter.start.val ≤ 32) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 1)
    (hinv : ∀ K < iter.start.val * 1, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 1 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 32, ∀ t < 8, r.val[K]!.val.testBit t = encBit 1 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 1 8 1 32 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Encoding, `D = 4` -/

theorem pack_chunk_4_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 2 ≤ 256) (hend : iter.end.val = 2) (hstart : iter.start.val ≤ 2)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 4)
    (hx : ∀ q, x.val.testBit q = chunkBit 4 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U4BaseFieldU4_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 4 vals.val start.val 2 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U4BaseFieldU4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 4 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 2 := by omega
    rw [this] at hx; exact hx
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_4_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 2 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 4) :
    module_lattice.encoding.pack_chunk_BaseField_U4BaseFieldU4 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 4 vals.val start.val 2 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U4BaseFieldU4
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_4_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_4_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 128#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 1) (hend : iter.end.val = 1) (hst : iter.start.val ≤ 1)
    (hc : c.val * 1 + 1 ≤ 128) :
    module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 128, r.val[K]! = if c.val * 1 + iter.start.val ≤ K ∧ K < c.val * 1 + 1 then
        xb.val[K - c.val * 1]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U128_IndexMut_usize.index_mut_u8_usize_U128U8UsizeU128]
    step*
    rw [index_mut_u8_usize_U128_back_post, h1] at r_post
    exact enc_inner_step 128 1 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 1 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_4_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 128#usize)
    (hvs : val_step.val = 2) (hbs : byte_step.val = 1) (hend : iter.end.val = 128)
    (hst : iter.start.val ≤ 128) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 4)
    (hinv : ∀ K < iter.start.val * 1, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 4 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 128, ∀ t < 8, r.val[K]!.val.testBit t = encBit 4 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 4 2 1 128 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 128 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Encoding, `D = 5` -/

theorem pack_chunk_5_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 8 ≤ 256) (hend : iter.end.val = 8) (hstart : iter.start.val ≤ 8)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 5)
    (hx : ∀ q, x.val.testBit q = chunkBit 5 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U5BaseFieldU5_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 5 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U5BaseFieldU5_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 5 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 8 := by omega
    rw [this] at hx; exact hx
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_5_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 8 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 5) :
    module_lattice.encoding.pack_chunk_BaseField_U5BaseFieldU5 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 5 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U5BaseFieldU5
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_5_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_5_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 160#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 5) (hend : iter.end.val = 5) (hst : iter.start.val ≤ 5)
    (hc : c.val * 5 + 5 ≤ 160) :
    module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 160, r.val[K]! = if c.val * 5 + iter.start.val ≤ K ∧ K < c.val * 5 + 5 then
        xb.val[K - c.val * 5]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U160_IndexMut_usize.index_mut_u8_usize_U160U8UsizeU160]
    step*
    rw [index_mut_u8_usize_U160_back_post, h1] at r_post
    exact enc_inner_step 160 5 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 5 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_5_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 160#usize)
    (hvs : val_step.val = 8) (hbs : byte_step.val = 5) (hend : iter.end.val = 32)
    (hst : iter.start.val ≤ 32) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 5)
    (hinv : ∀ K < iter.start.val * 5, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 5 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 160, ∀ t < 8, r.val[K]!.val.testBit t = encBit 5 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 5 8 5 160 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Encoding, `D = 10` -/

theorem pack_chunk_10_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 4 ≤ 256) (hend : iter.end.val = 4) (hstart : iter.start.val ≤ 4)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 10)
    (hx : ∀ q, x.val.testBit q = chunkBit 10 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U10BaseFieldU10_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 10 vals.val start.val 4 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U10BaseFieldU10_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 10 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 4 := by omega
    rw [this] at hx; exact hx
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_10_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 4 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 10) :
    module_lattice.encoding.pack_chunk_BaseField_U10BaseFieldU10 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 10 vals.val start.val 4 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U10BaseFieldU10
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_10_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_10_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 320#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 5) (hend : iter.end.val = 5) (hst : iter.start.val ≤ 5)
    (hc : c.val * 5 + 5 ≤ 320) :
    module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 320, r.val[K]! = if c.val * 5 + iter.start.val ≤ K ∧ K < c.val * 5 + 5 then
        xb.val[K - c.val * 5]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U320_IndexMut_usize.index_mut_u8_usize_U320U8UsizeU320]
    step*
    rw [index_mut_u8_usize_U320_back_post, h1] at r_post
    exact enc_inner_step 320 5 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 5 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_10_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 320#usize)
    (hvs : val_step.val = 4) (hbs : byte_step.val = 5) (hend : iter.end.val = 64)
    (hst : iter.start.val ≤ 64) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 10)
    (hinv : ∀ K < iter.start.val * 5, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 10 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 320, ∀ t < 8, r.val[K]!.val.testBit t = encBit 10 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 10 4 5 320 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 64 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Encoding, `D = 11` -/

theorem pack_chunk_11_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 8 ≤ 256) (hend : iter.end.val = 8) (hstart : iter.start.val ≤ 8)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 11)
    (hx : ∀ q, x.val.testBit q = chunkBit 11 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U11BaseFieldU11_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 11 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U11BaseFieldU11_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 11 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 8 := by omega
    rw [this] at hx; exact hx
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_11_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 8 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 11) :
    module_lattice.encoding.pack_chunk_BaseField_U11BaseFieldU11 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 11 vals.val start.val 8 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U11BaseFieldU11
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_11_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_11_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 352#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 11) (hend : iter.end.val = 11) (hst : iter.start.val ≤ 11)
    (hc : c.val * 11 + 11 ≤ 352) :
    module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 352, r.val[K]! = if c.val * 11 + iter.start.val ≤ K ∧ K < c.val * 11 + 11 then
        xb.val[K - c.val * 11]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U352_IndexMut_usize.index_mut_u8_usize_U352U8UsizeU352]
    step*
    rw [index_mut_u8_usize_U352_back_post, h1] at r_post
    exact enc_inner_step 352 11 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 11 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_11_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 352#usize)
    (hvs : val_step.val = 8) (hbs : byte_step.val = 11) (hend : iter.end.val = 32)
    (hst : iter.start.val ≤ 32) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 11)
    (hinv : ∀ K < iter.start.val * 11, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 11 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 352, ∀ t < 8, r.val[K]!.val.testBit t = encBit 11 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 11 8 11 352 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Encoding, `D = 12` -/

theorem pack_chunk_12_loop_spec (iter : core.ops.range.Range Usize) (vals : Coeffs) (start : Usize)
    (x : U128) (hs : start.val + 2 ≤ 256) (hend : iter.end.val = 2) (hstart : iter.start.val ≤ 2)
    (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 12)
    (hx : ∀ q, x.val.testBit q = chunkBit 12 vals.val start.val iter.start.val q) :
    module_lattice.encoding.pack_chunk_BaseField_U12BaseFieldU12_loop iter vals start x
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 12 vals.val start.val 2 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U12BaseFieldU12_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Elem_BaseField_U256_Index_usize.index_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256,
      U16.Insts.CoreConvertIntoU128.into, typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0]
    step*
    intro q
    rw [x1_post, UScalar.val_or, i3_post, i2_post, h1]
    simp only [UScalar.cast_val_eq, U128.size, U128.numBits]
    have hc : ebf.val % 2 ^ UScalarTy.U128.numBits = ebf.val := Nat.mod_eq_of_lt (by scalar_tac)
    have hn : UScalarTy.U128.numBits = 128 := rfl
    have hebf : ebf.val = vals.val[start.val + iter.start.val]!.val := by
      rw [ebf_post, ← i_post, getElem!_pos]
    rw [hc, hn]
    exact chunkBit_step 12 vals.val start.val iter.start.val x.val ebf.val hebf
      (hebf ▸ hv _ (by omega)) hx (by omega) q
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    have : iter.start.val = 2 := by omega
    rw [this] at hx; exact hx
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem pack_chunk_12_spec (vals : Coeffs) (start : Usize)
    (hs : start.val + 2 ≤ 256) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 12) :
    module_lattice.encoding.pack_chunk_BaseField_U12BaseFieldU12 vals start
      ⦃ r => ∀ q, r.val.testBit q = chunkBit 12 vals.val start.val 2 q ⦄ := by
  unfold module_lattice.encoding.pack_chunk_BaseField_U12BaseFieldU12
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ r, hr ⟩ ← pack_chunk_12_loop_spec
  · intro q; simp [chunkBit]
  · exact hr _

@[step] theorem byte_encode_12_inner_spec (iter : core.ops.range.Range Usize) (byte_step : Usize)
    (bytes : Std.Array U8 384#usize) (c : Usize) (xb : Std.Array U8 16#usize)
    (hbs : byte_step.val = 3) (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3)
    (hc : c.val * 3 + 3 ≤ 384) :
    module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12_loop0_loop0 iter byte_step bytes c xb
      ⦃ r => ∀ K < 384, r.val[K]! = if c.val * 3 + iter.start.val ≤ K ∧ K < c.val * 3 + 3 then
        xb.val[K - c.val * 3]! else bytes.val[K]! ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12_loop0_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_u8_16,
      hybrid_array.Array_u8_U384_IndexMut_usize.index_mut_u8_usize_U384U8UsizeU384]
    step*
    rw [index_mut_u8_usize_U384_back_post, h1] at r_post
    exact enc_inner_step 384 3 c.val iter.start.val bytes.val r.val xb.val i2 i _ bytes rfl rfl
      (by simp [*]) (by omega) (by rw [i_post, getElem!_pos]) r_post K K_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK
    rw [if_neg (by omega)]
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

theorem byte_encode_12_outer_spec (iter : core.ops.range.Range Usize) (vals : Coeffs)
    (val_step byte_step : Usize) (bytes : Std.Array U8 384#usize)
    (hvs : val_step.val = 2) (hbs : byte_step.val = 3) (hend : iter.end.val = 128)
    (hst : iter.start.val ≤ 128) (hv : ∀ i (hi : i < 256), vals.val[i]!.val < 2 ^ 12)
    (hinv : ∀ K < iter.start.val * 3, ∀ t < 8,
      bytes.val[K]!.val.testBit t = encBit 12 vals.val (8 * K + t)) :
    module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12_loop0 iter vals val_step byte_step bytes
      ⦃ r => ∀ K < 384, ∀ t < 8, r.val[K]!.val.testBit t = encBit 12 vals.val (8 * K + t) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hvs] at i1_post
    rw [xb_post, Nat.add_zero] at bytes1_post
    exact enc_chunk_step 12 2 3 384 (by norm_num) (by norm_num) vals.val iter.start.val i1 i1_post
      bytes.val bytes1.val bytes1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro K hK t ht
    exact hinv K (by omega) t ht
termination_by 128 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 1` -/

theorem unpack_chunk_1_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 32#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 1) (hst : iter.start.val ≤ 1) (hs : start.val + 1 ≤ 32) :
    module_lattice.encoding.unpack_chunk_U1U1_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 1 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U1U1_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U32_Index_usize.index_u8_usize_U32U8UsizeU32]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 1 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 1 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_1_spec (bytes : Std.Array U8 32#usize) (start : Usize)
    (hs : start.val + 1 ≤ 32) :
    module_lattice.encoding.unpack_chunk_U1U1 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 1) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U1U1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_1_loop_spec
  exact unpack_bits 1 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_1_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 1) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 1 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val ≤ 8) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 8 + iter.start.val ≤ idx → idx < c.val * 8 + 8 →
          r.val[idx]!.val = decVal 1 x.val (idx - c.val * 8)) ∧
        (¬ (c.val * 8 + iter.start.val ≤ idx ∧ idx < c.val * 8 + 8) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 1 8 c.val iter.start.val x.val vals r.val i3 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i1_post, i_post, hmask, hD, dec_val_lt12 1 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_1_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 1) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 1 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val = 0) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 8 ≤ i → i < c.val * 8 + 8 →
          r.val[i]!.val = decVal 1 x.val (i - c.val * 8)) ∧
        (¬ (c.val * 8 ≤ i ∧ i < c.val * 8 + 8) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_1_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_1_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 32#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 1) (hvs : val_step.val = 8) (hbs : byte_step.val = 1)
    (hmask : mask.val = 2 ^ 1 - 1) (hend : iter.end.val = 32) (hst : iter.start.val ≤ 32)
    (hinv : ∀ i < iter.start.val * 8, DecOK 1 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 1 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hbs] at x_post
    exact dec_chunk_step 1 8 1 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 4` -/

theorem unpack_chunk_4_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 128#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 1) (hst : iter.start.val ≤ 1) (hs : start.val + 1 ≤ 128) :
    module_lattice.encoding.unpack_chunk_U4U4_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 1 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U4U4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U128_Index_usize.index_u8_usize_U128U8UsizeU128]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 1 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 1 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_4_spec (bytes : Std.Array U8 128#usize) (start : Usize)
    (hs : start.val + 1 ≤ 128) :
    module_lattice.encoding.unpack_chunk_U4U4 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 1) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U4U4
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_4_loop_spec
  exact unpack_bits 1 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_4_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 4) (hvs : val_step.val = 2) (hmask : mask.val = 2 ^ 4 - 1)
    (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2) (hc : c.val * 2 + 2 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 2 + iter.start.val ≤ idx → idx < c.val * 2 + 2 →
          r.val[idx]!.val = decVal 4 x.val (idx - c.val * 2)) ∧
        (¬ (c.val * 2 + iter.start.val ≤ idx ∧ idx < c.val * 2 + 2) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 4 2 c.val iter.start.val x.val vals r.val i4 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i2_post, i1_post, hmask, hD, dec_val_lt12 4 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_4_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 4) (hvs : val_step.val = 2) (hmask : mask.val = 2 ^ 4 - 1)
    (hend : iter.end.val = 2) (hst : iter.start.val = 0) (hc : c.val * 2 + 2 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 2 ≤ i → i < c.val * 2 + 2 →
          r.val[i]!.val = decVal 4 x.val (i - c.val * 2)) ∧
        (¬ (c.val * 2 ≤ i ∧ i < c.val * 2 + 2) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_4_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_4_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 128#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 4) (hvs : val_step.val = 2) (hbs : byte_step.val = 1)
    (hmask : mask.val = 2 ^ 4 - 1) (hend : iter.end.val = 128) (hst : iter.start.val ≤ 128)
    (hinv : ∀ i < iter.start.val * 2, DecOK 4 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 4 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i1_post, hbs] at x_post
    exact dec_chunk_step 4 2 1 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 128 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 5` -/

theorem unpack_chunk_5_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 160#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 5) (hst : iter.start.val ≤ 5) (hs : start.val + 5 ≤ 160) :
    module_lattice.encoding.unpack_chunk_U5U5_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 5 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U5U5_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U160_Index_usize.index_u8_usize_U160U8UsizeU160]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 5 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 5 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_5_spec (bytes : Std.Array U8 160#usize) (start : Usize)
    (hs : start.val + 5 ≤ 160) :
    module_lattice.encoding.unpack_chunk_U5U5 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 5) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U5U5
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_5_loop_spec
  exact unpack_bits 5 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_5_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 5) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 5 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val ≤ 8) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 8 + iter.start.val ≤ idx → idx < c.val * 8 + 8 →
          r.val[idx]!.val = decVal 5 x.val (idx - c.val * 8)) ∧
        (¬ (c.val * 8 + iter.start.val ≤ idx ∧ idx < c.val * 8 + 8) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 5 8 c.val iter.start.val x.val vals r.val i3 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i1_post, i_post, hmask, hD, dec_val_lt12 5 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_5_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 5) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 5 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val = 0) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 8 ≤ i → i < c.val * 8 + 8 →
          r.val[i]!.val = decVal 5 x.val (i - c.val * 8)) ∧
        (¬ (c.val * 8 ≤ i ∧ i < c.val * 8 + 8) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_5_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_5_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 160#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 5) (hvs : val_step.val = 8) (hbs : byte_step.val = 5)
    (hmask : mask.val = 2 ^ 5 - 1) (hend : iter.end.val = 32) (hst : iter.start.val ≤ 32)
    (hinv : ∀ i < iter.start.val * 8, DecOK 5 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 5 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hbs] at x_post
    exact dec_chunk_step 5 8 5 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 6` -/

theorem unpack_chunk_6_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 192#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3) (hs : start.val + 3 ≤ 192) :
    module_lattice.encoding.unpack_chunk_U6U6_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 3 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U6U6_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U192_Index_usize.index_u8_usize_U192U8UsizeU192]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 3 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_6_spec (bytes : Std.Array U8 192#usize) (start : Usize)
    (hs : start.val + 3 ≤ 192) :
    module_lattice.encoding.unpack_chunk_U6U6 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 3) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U6U6
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_6_loop_spec
  exact unpack_bits 3 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_6_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 6) (hvs : val_step.val = 4) (hmask : mask.val = 2 ^ 6 - 1)
    (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4) (hc : c.val * 4 + 4 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 4 + iter.start.val ≤ idx → idx < c.val * 4 + 4 →
          r.val[idx]!.val = decVal 6 x.val (idx - c.val * 4)) ∧
        (¬ (c.val * 4 + iter.start.val ≤ idx ∧ idx < c.val * 4 + 4) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 6 4 c.val iter.start.val x.val vals r.val i4 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i2_post, i1_post, hmask, hD, dec_val_lt12 6 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_6_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 6) (hvs : val_step.val = 4) (hmask : mask.val = 2 ^ 6 - 1)
    (hend : iter.end.val = 4) (hst : iter.start.val = 0) (hc : c.val * 4 + 4 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 4 ≤ i → i < c.val * 4 + 4 →
          r.val[i]!.val = decVal 6 x.val (i - c.val * 4)) ∧
        (¬ (c.val * 4 ≤ i ∧ i < c.val * 4 + 4) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_6_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_6_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 192#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 6) (hvs : val_step.val = 4) (hbs : byte_step.val = 3)
    (hmask : mask.val = 2 ^ 6 - 1) (hend : iter.end.val = 64) (hst : iter.start.val ≤ 64)
    (hinv : ∀ i < iter.start.val * 4, DecOK 6 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 6 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i1_post, hbs] at x_post
    exact dec_chunk_step 6 4 3 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 64 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 10` -/

theorem unpack_chunk_10_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 320#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 5) (hst : iter.start.val ≤ 5) (hs : start.val + 5 ≤ 320) :
    module_lattice.encoding.unpack_chunk_U10U10_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 5 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U10U10_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U320_Index_usize.index_u8_usize_U320U8UsizeU320]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 5 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 5 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_10_spec (bytes : Std.Array U8 320#usize) (start : Usize)
    (hs : start.val + 5 ≤ 320) :
    module_lattice.encoding.unpack_chunk_U10U10 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 5) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U10U10
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_10_loop_spec
  exact unpack_bits 5 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_10_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 10) (hvs : val_step.val = 4) (hmask : mask.val = 2 ^ 10 - 1)
    (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4) (hc : c.val * 4 + 4 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 4 + iter.start.val ≤ idx → idx < c.val * 4 + 4 →
          r.val[idx]!.val = decVal 10 x.val (idx - c.val * 4)) ∧
        (¬ (c.val * 4 + iter.start.val ≤ idx ∧ idx < c.val * 4 + 4) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 10 4 c.val iter.start.val x.val vals r.val i4 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i2_post, i1_post, hmask, hD, dec_val_lt12 10 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_10_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 10) (hvs : val_step.val = 4) (hmask : mask.val = 2 ^ 10 - 1)
    (hend : iter.end.val = 4) (hst : iter.start.val = 0) (hc : c.val * 4 + 4 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 4 ≤ i → i < c.val * 4 + 4 →
          r.val[i]!.val = decVal 10 x.val (i - c.val * 4)) ∧
        (¬ (c.val * 4 ≤ i ∧ i < c.val * 4 + 4) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_10_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_10_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 320#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 10) (hvs : val_step.val = 4) (hbs : byte_step.val = 5)
    (hmask : mask.val = 2 ^ 10 - 1) (hend : iter.end.val = 64) (hst : iter.start.val ≤ 64)
    (hinv : ∀ i < iter.start.val * 4, DecOK 10 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 10 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i1_post, hbs] at x_post
    exact dec_chunk_step 10 4 5 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 64 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 11` -/

theorem unpack_chunk_11_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 352#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 11) (hst : iter.start.val ≤ 11) (hs : start.val + 11 ≤ 352) :
    module_lattice.encoding.unpack_chunk_U11U11_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 11 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U11U11_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U352_Index_usize.index_u8_usize_U352U8UsizeU352]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 11 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 11 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_11_spec (bytes : Std.Array U8 352#usize) (start : Usize)
    (hs : start.val + 11 ≤ 352) :
    module_lattice.encoding.unpack_chunk_U11U11 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 11) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U11U11
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_11_loop_spec
  exact unpack_bits 11 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_11_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 11) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 11 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val ≤ 8) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 8 + iter.start.val ≤ idx → idx < c.val * 8 + 8 →
          r.val[idx]!.val = decVal 11 x.val (idx - c.val * 8)) ∧
        (¬ (c.val * 8 + iter.start.val ≤ idx ∧ idx < c.val * 8 + 8) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11_loop0_loop0
  have hne : ¬ (Dp = 12#usize) := by intro h; rw [h] at hD; simp at hD
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hne, if_false,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
    refine dec_inner_step 11 8 c.val iter.start.val x.val vals r.val i3 v1 (by simp [*]) (by omega) ?_
      r_post idx idx_post
    rw [v1_post, val_post, i1_post, i_post, hmask, hD, dec_val_lt12 11 (by norm_num)]
    rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 8 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_11_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 11) (hvs : val_step.val = 8) (hmask : mask.val = 2 ^ 11 - 1)
    (hend : iter.end.val = 8) (hst : iter.start.val = 0) (hc : c.val * 8 + 8 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 8 ≤ i → i < c.val * 8 + 8 →
          r.val[i]!.val = decVal 11 x.val (i - c.val * 8)) ∧
        (¬ (c.val * 8 ≤ i ∧ i < c.val * 8 + 8) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_11_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_11_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 352#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 11) (hvs : val_step.val = 8) (hbs : byte_step.val = 11)
    (hmask : mask.val = 2 ^ 11 - 1) (hend : iter.end.val = 32) (hst : iter.start.val ≤ 32)
    (hinv : ∀ i < iter.start.val * 8, DecOK 11 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 11 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i_post, hbs] at x_post
    exact dec_chunk_step 11 8 11 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ### Decoding, `D = 12` -/

theorem unpack_chunk_12_loop_spec (iter : core.ops.range.Range Usize) (bytes : Std.Array U8 384#usize)
    (start : Usize) (xb : Std.Array U8 16#usize)
    (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3) (hs : start.val + 3 ≤ 384) :
    module_lattice.encoding.unpack_chunk_U12U12_loop iter bytes start xb
      ⦃ r => ∀ k < 16, r.val[k]! = if iter.start.val ≤ k ∧ k < 3 then bytes.val[start.val + k]!
        else xb.val[k]! ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U12U12_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, aeneas_mono.array_index_mut_u8_16,
      hybrid_array.Array_u8_U384_Index_usize.index_u8_usize_U384U8UsizeU384]
    step*
    rw [array_index_mut_u8_16_back_post, h1] at r_post
    exact unpack_step 3 iter.start.val xb bytes.val r.val start.val iter.start rfl i1
      (by rw [i1_post]; exact getElem_eq_getElem!' _ _ _ _ i_post) (by omega) r_post k k_post
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem unpack_chunk_12_spec (bytes : Std.Array U8 384#usize) (start : Usize)
    (hs : start.val + 3 ≤ 384) :
    module_lattice.encoding.unpack_chunk_U12U12 bytes start
      ⦃ x => ∀ q, x.val.testBit q =
        (decide (q < 8 * 3) && bytes.val[start.val + q / 8]!.val.testBit (q % 8)) ⦄ := by
  unfold module_lattice.encoding.unpack_chunk_U12U12
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  let* ⟨ xb, hxb ⟩ ← unpack_chunk_12_loop_spec
  exact unpack_bits 3 (by norm_num) bytes.val start.val xb (by simpa using hxb)

theorem byte_decode_12_inner_spec (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 12) (hvs : val_step.val = 2) (hmask : mask.val = 2 ^ 12 - 1)
    (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2) (hc : c.val * 2 + 2 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ idx < 256, (c.val * 2 + iter.start.val ≤ idx → idx < c.val * 2 + 2 →
          r.val[idx]!.val = decVal 12 x.val (idx - c.val * 2)) ∧
        (¬ (c.val * 2 + iter.start.val ≤ idx ∧ idx < c.val * 2 + 2) → r.val[idx]! = vals.val[idx]!) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12_loop0_loop0
  have h12 : Dp = 12#usize := by scalar_tac
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, h12, if_true,
      hybrid_array.Array_Elem_BaseField_U256_IndexMut_usize.index_mut_Elem_BaseField_usize_U256Elem_BaseFieldUsizeU256]
    step*
    · rw [v_post, hmask]; exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    · rw [index_mut_Elem_BaseField_usize_U256_back_post, h1] at r_post
      refine dec_inner_step 12 2 c.val iter.start.val x.val vals r.val i4 v1 (by simp [*]) (by omega) ?_
        r_post idx idx_post
      rw [v1_post, v_post, val_post, i2_post, i1_post, hmask, dec_val_12]
      rfl
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact ⟨fun h' h'' => by omega, fun _ => by first | rfl | trivial⟩
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

@[step] theorem byte_decode_12_inner_spec' (Dp : Usize) (iter : core.ops.range.Range Usize) (val_step : Usize)
    (mask : U16) (vals : Coeffs) (c : Usize) (x : U128)
    (hD : Dp.val = 12) (hvs : val_step.val = 2) (hmask : mask.val = 2 ^ 12 - 1)
    (hend : iter.end.val = 2) (hst : iter.start.val = 0) (hc : c.val * 2 + 2 ≤ 256) :
    module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12_loop0_loop0 Dp iter val_step mask vals c x
      ⦃ r => ∀ i < 256, (c.val * 2 ≤ i → i < c.val * 2 + 2 →
          r.val[i]!.val = decVal 12 x.val (i - c.val * 2)) ∧
        (¬ (c.val * 2 ≤ i ∧ i < c.val * 2 + 2) → r.val[i]! = vals.val[i]!) ⦄ := by
  have := byte_decode_12_inner_spec Dp iter val_step mask vals c x hD hvs hmask hend (by omega) hc
  simpa [hst] using this

theorem byte_decode_12_outer_spec (Dp : Usize) (iter : core.ops.range.Range Usize)
    (bytes : Std.Array U8 384#usize) (val_step byte_step : Usize) (mask : U16) (vals : Coeffs)
    (hD : Dp.val = 12) (hvs : val_step.val = 2) (hbs : byte_step.val = 3)
    (hmask : mask.val = 2 ^ 12 - 1) (hend : iter.end.val = 128) (hst : iter.start.val ≤ 128)
    (hinv : ∀ i < iter.start.val * 2, DecOK 12 bytes.val i vals.val[i]!) :
    module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12_loop0 Dp iter bytes val_step byte_step mask vals
      ⦃ r => ∀ i < 256, DecOK 12 bytes.val i r.val[i]! ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12_loop0
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
    step*
    rw [h1]
    rw [i1_post, hbs] at x_post
    exact dec_chunk_step 12 2 3 (by norm_num) (by norm_num) bytes.val iter.start.val x.val x_post
      vals.val vals1.val vals1_post hinv (by omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro i hi
    exact hinv i (by omega)
termination_by 128 - iter.start.val
decreasing_by scalar_decr_tac

/-! # Interface lemmas -/


-- INTERFACE
@[step] theorem byte_encode_spec_1 (a : Coeffs)
    (ha : a.Bounded (m 1)) :
    module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1 a
      ⦃ r => arrayToBytes r = ByteEncode 1 (a.toVector (m 1)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U1BaseFieldU1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U32_Default.default_u8_U32U8U32,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_1_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 1 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_encode_spec_4 (a : Coeffs)
    (ha : a.Bounded (m 4)) :
    module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4 a
      ⦃ r => arrayToBytes r = ByteEncode 4 (a.toVector (m 4)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U4BaseFieldU4
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U128_Default.default_u8_U128U8U128,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_4_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 4 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_encode_spec_5 (a : Coeffs)
    (ha : a.Bounded (m 5)) :
    module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5 a
      ⦃ r => arrayToBytes r = ByteEncode 5 (a.toVector (m 5)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U5BaseFieldU5
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U160_Default.default_u8_U160U8U160,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_5_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 5 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_encode_spec_10 (a : Coeffs)
    (ha : a.Bounded (m 10)) :
    module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10 a
      ⦃ r => arrayToBytes r = ByteEncode 10 (a.toVector (m 10)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U10BaseFieldU10
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U320_Default.default_u8_U320U8U320,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_10_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 10 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_encode_spec_11 (a : Coeffs)
    (ha : a.Bounded (m 11)) :
    module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11 a
      ⦃ r => arrayToBytes r = ByteEncode 11 (a.toVector (m 11)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U11BaseFieldU11
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U352_Default.default_u8_U352U8U352,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_11_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 11 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_encode_spec_12 (a : Coeffs)
    (ha : a.Bounded (m 12)) :
    module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12 a
      ⦃ r => arrayToBytes r = ByteEncode 12 (a.toVector (m 12)) ⦄ := by
  unfold module_lattice.encoding.byte_encode_BaseField_U12BaseFieldU12
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0,
    hybrid_array.Array_u8_U384_Default.default_u8_U384U8U384,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← byte_encode_12_outer_spec
  · exact bounded_lt (by decide) a ha
  · apply Vector.ext
    intro k hk
    exact encode_glue 12 (by decide) a ha r rfl hr k hk

-- INTERFACE
@[step] theorem byte_decode_spec_1 (b : Std.Array U8 32#usize) :
    module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1 b
      ⦃ (r : Coeffs) => r.Bounded (m 1) ∧ r.toVector (m 1) = ByteDecode (d := 1) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U1BaseFieldU1
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_1_outer_spec
  exact decode_glue 1 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_4 (b : Std.Array U8 128#usize) :
    module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4 b
      ⦃ (r : Coeffs) => r.Bounded (m 4) ∧ r.toVector (m 4) = ByteDecode (d := 4) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U4BaseFieldU4
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_4_outer_spec
  exact decode_glue 4 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_5 (b : Std.Array U8 160#usize) :
    module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5 b
      ⦃ (r : Coeffs) => r.Bounded (m 5) ∧ r.toVector (m 5) = ByteDecode (d := 5) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U5BaseFieldU5
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_5_outer_spec
  exact decode_glue 5 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_6 (b : Std.Array U8 192#usize) :
    module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6 b
      ⦃ (r : Coeffs) => r.Bounded (m 6) ∧ r.toVector (m 6) = ByteDecode (d := 6) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U6BaseFieldU6
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_6_outer_spec
  exact decode_glue 6 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_10 (b : Std.Array U8 320#usize) :
    module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10 b
      ⦃ (r : Coeffs) => r.Bounded (m 10) ∧ r.toVector (m 10) = ByteDecode (d := 10) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U10BaseFieldU10
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_10_outer_spec
  exact decode_glue 10 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_11 (b : Std.Array U8 352#usize) :
    module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11 b
      ⦃ (r : Coeffs) => r.Bounded (m 11) ∧ r.toVector (m 11) = ByteDecode (d := 11) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U11BaseFieldU11
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_11_outer_spec
  exact decode_glue 11 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem byte_decode_spec_12 (b : Std.Array U8 384#usize) :
    module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12 b
      ⦃ (r : Coeffs) => r.Bounded (m 12) ∧ r.toVector (m 12) = ByteDecode (d := 12) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.byte_decode_BaseField_U12BaseFieldU12
  simp only [typenum.uint.U1_Unsigned.USIZE_U1UTermB1, typenum.uint.U2_Unsigned.USIZE_U2U1B0, typenum.uint.U3_Unsigned.USIZE_U3U1B1, typenum.uint.U4_Unsigned.USIZE_U4U2B0, typenum.uint.U5_Unsigned.USIZE_U5U2B1, typenum.uint.U6_Unsigned.USIZE_U6U3B0, typenum.uint.U8_Unsigned.USIZE_U8U4B0, typenum.uint.U10_Unsigned.USIZE_U10U5B0, typenum.uint.U11_Unsigned.USIZE_U11U5B1, typenum.uint.U12_Unsigned.USIZE_U12U6B0, num_traits.identities.u16_One.one,
    hybrid_array.Array_Elem_BaseField_U256_Default.default_Elem_BaseField_U256Elem_BaseFieldU256,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    U16.Insts.CoreOpsBitShlUsize.shl]
  step*
  let* ⟨ r, hr ⟩ ← byte_decode_12_outer_spec
  exact decode_glue 12 _ (arrayToBytes b) b.val (fun k hk => arrayToBytes_getElem b k hk) r hr

-- INTERFACE
@[step] theorem poly_encode_spec_1 (a : Coeffs)
    (ha : a.Bounded (m 1)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U1.encode_BaseField_U1BaseFieldU1 a
      ⦃ r => arrayToBytes r = ByteEncode 1 (a.toVector (m 1)) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U1.encode_BaseField_U1BaseFieldU1
  exact byte_encode_spec_1 a ha

-- INTERFACE
@[step] theorem poly_encode_spec_4 (a : Coeffs)
    (ha : a.Bounded (m 4)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U4.encode_BaseField_U4BaseFieldU4 a
      ⦃ r => arrayToBytes r = ByteEncode 4 (a.toVector (m 4)) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U4.encode_BaseField_U4BaseFieldU4
  exact byte_encode_spec_4 a ha

-- INTERFACE
@[step] theorem poly_encode_spec_5 (a : Coeffs)
    (ha : a.Bounded (m 5)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U5.encode_BaseField_U5BaseFieldU5 a
      ⦃ r => arrayToBytes r = ByteEncode 5 (a.toVector (m 5)) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U5.encode_BaseField_U5BaseFieldU5
  exact byte_encode_spec_5 a ha

-- INTERFACE
@[step] theorem poly_encode_spec_10 (a : Coeffs)
    (ha : a.Bounded (m 10)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U10.encode_BaseField_U10BaseFieldU10 a
      ⦃ r => arrayToBytes r = ByteEncode 10 (a.toVector (m 10)) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U10.encode_BaseField_U10BaseFieldU10
  exact byte_encode_spec_10 a ha

-- INTERFACE
@[step] theorem poly_encode_spec_11 (a : Coeffs)
    (ha : a.Bounded (m 11)) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U11.encode_BaseField_U11BaseFieldU11 a
      ⦃ r => arrayToBytes r = ByteEncode 11 (a.toVector (m 11)) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U11.encode_BaseField_U11BaseFieldU11
  exact byte_encode_spec_11 a ha

-- INTERFACE
@[step] theorem poly_decode_spec_1 (b : Std.Array U8 32#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U1.decode_BaseField_U1BaseFieldU1 b
      ⦃ (r : Coeffs) => r.Bounded (m 1) ∧ r.toVector (m 1) = ByteDecode (d := 1) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U1.decode_BaseField_U1BaseFieldU1
  step*

-- INTERFACE
@[step] theorem poly_decode_spec_4 (b : Std.Array U8 128#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U4.decode_BaseField_U4BaseFieldU4 b
      ⦃ (r : Coeffs) => r.Bounded (m 4) ∧ r.toVector (m 4) = ByteDecode (d := 4) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U4.decode_BaseField_U4BaseFieldU4
  step*

-- INTERFACE
@[step] theorem poly_decode_spec_5 (b : Std.Array U8 160#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U5.decode_BaseField_U5BaseFieldU5 b
      ⦃ (r : Coeffs) => r.Bounded (m 5) ∧ r.toVector (m 5) = ByteDecode (d := 5) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U5.decode_BaseField_U5BaseFieldU5
  step*

-- INTERFACE
@[step] theorem poly_decode_spec_6 (b : Std.Array U8 192#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U6.decode_BaseField_U6BaseFieldU6 b
      ⦃ (r : Coeffs) => r.Bounded (m 6) ∧ r.toVector (m 6) = ByteDecode (d := 6) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U6.decode_BaseField_U6BaseFieldU6
  step*

-- INTERFACE
@[step] theorem poly_decode_spec_10 (b : Std.Array U8 320#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U10.decode_BaseField_U10BaseFieldU10 b
      ⦃ (r : Coeffs) => r.Bounded (m 10) ∧ r.toVector (m 10) = ByteDecode (d := 10) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U10.decode_BaseField_U10BaseFieldU10
  step*

-- INTERFACE
@[step] theorem poly_decode_spec_11 (b : Std.Array U8 352#usize) :
    module_lattice.encoding.Polynomial_BaseField_Encode_U11.decode_BaseField_U11BaseFieldU11 b
      ⦃ (r : Coeffs) => r.Bounded (m 11) ∧ r.toVector (m 11) = ByteDecode (d := 11) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Polynomial_BaseField_Encode_U11.decode_BaseField_U11BaseFieldU11
  step*

-- INTERFACE
@[step] theorem ntt_poly_encode_spec_12 (a : Coeffs)
    (ha : a.Bounded q) :
    module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.encode_BaseField_U12BaseFieldU12 a
      ⦃ r => arrayToBytes r = ByteEncode 12 (a.toVector q) ⦄ := by
  unfold module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.encode_BaseField_U12BaseFieldU12
  exact byte_encode_spec_12 a ha

-- INTERFACE
@[step] theorem ntt_poly_decode_spec_12 (b : Std.Array U8 384#usize) :
    module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.decode_BaseField_U12BaseFieldU12 b
      ⦃ (r : Coeffs) => r.Bounded q ∧ r.toVector q = ByteDecode (d := 12) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.NttPolynomial_BaseField_Encode_U12.decode_BaseField_U12BaseFieldU12
  step*

/-! # Helper lemmas for vectors -/

/-! ## Vectors -/

abbrev Bytes320 := Std.Array U8 320#usize
abbrev Bytes352 := Std.Array U8 352#usize
abbrev Bytes384 := Std.Array U8 384#usize


theorem list_flatten_getElem! {α : Type} [Inhabited α] (n : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = n) → ∀ i, i < l.length * n →
      l.flatten[i]! = (l[i / n]!)[i % n]! := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons x l ih =>
    intro hl i hi
    have hx : x.length = n := hl x (by simp)
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at hi
      · exact h
    have hl' : ∀ y ∈ l, y.length = n := fun y hy => hl y (by simp [hy])
    have hlen : l.flatten.length = l.length * n := by
      rw [List.length_flatten, List.map_congr_left (g := fun _ => n) (fun y hy => hl' y hy)]; simp
    simp only [List.length_cons, Nat.succ_mul] at hi
    rw [List.flatten_cons]
    by_cases h : i < n
    · rw [getElem!_pos (x ++ l.flatten) i (by simp; omega), List.getElem_append_left (by omega),
        Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp [getElem!_pos x i (by omega)]
    · obtain ⟨i', rfl⟩ : ∃ i', i = n + i' := ⟨i - n, by omega⟩
      rw [getElem!_pos (x ++ l.flatten) (n + i') (by simp [hx, hlen]; omega),
        List.getElem_append_right (by omega)]
      simp only [hx, Nat.add_sub_cancel_left]
      rw [← getElem!_pos l.flatten i' (by omega), ih hl' i' (by omega),
        Nat.add_div_left _ hn, Nat.add_mod_left]
      simp

theorem flatten_getElem! {α : Type} [Inhabited α] {n k N : Usize} (polys : Std.Array (Std.Array α n) k)
    (h : k.val * n.val = N.val) (i : ℕ) (hi : i < N.val) :
    (Model.flatten polys h).val[i]! = (polys.val[i / n.val]!).val[i % n.val]! := by
  simp only [Model.flatten, Std.Array.from_val]
  have hn : 0 < n.val := by
    rcases Nat.eq_zero_or_pos n.val with h' | h'
    · rw [h', Nat.mul_zero] at h; omega
    · exact h'
  rw [list_flatten_getElem! n.val _ (by simp) i (by simp; omega)]
  have hj : i / n.val < polys.val.length := by simp; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  rw [getElem!_pos (polys.val.map (·.val)) _ (by simpa using hj), getElem!_pos polys.val _ hj,
    List.getElem_map]

theorem PolyVector.ByteEncode_getElem (d : ℕ) {k : K} (v : PolyVector (m d) k) (hd : 1 ≤ d ∧ d ≤ 12)
    (i : ℕ) (hi : i < 32 * d * k) :
    (PolyVector.ByteEncode d v hd)[i] =
      (ByteEncode d (v[i / (32 * d)]'(Nat.div_lt_of_lt_mul hi)).coeffs hd)[i % (32 * d)]'(
          Nat.mod_lt _ (by omega)) := by
  simp [PolyVector.ByteEncode]

theorem ByteEncode₁₂_getElem {k : K} (v : NTTVector k) (i : ℕ) (hi : i < 384 * k) :
    (ByteEncode₁₂ v)[i] =
      (ByteEncode 12 (v[i / 384]'(Nat.div_lt_of_lt_mul hi)).coeffs)[i % 384]'(
          Nat.mod_lt _ (by omega)) := by
  simp [ByteEncode₁₂]

theorem toPolyVec_coeffs (mm : ℕ) {n : Usize} (v : Std.Array Coeffs n) (j : ℕ) (hj : j < n.val) :
    (toPolyVec mm v)[j].coeffs = (v.val[j]!).toVector mm := by
  simp only [toPolyVec, Vector.getElem_ofFn, Coeffs.toPoly]
  rw [getElem!_pos v.val j (by simpa using hj)]

theorem toNTTVec_coeffs {n : Usize} (v : Std.Array Coeffs n) (j : ℕ) (hj : j < n.val) :
    (toNTTVec v)[j].coeffs = (v.val[j]!).toVector q := by
  simp only [toNTTVec, Vector.getElem_ofFn, Coeffs.toTq]
  rw [getElem!_pos v.val j (by simpa using hj)]

theorem vec_encode_glue (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 12) {kk : K} (w : PolyVector (m d) kk)
    (F : ℕ → Vector (ZMod (m d)) 256) (hw : ∀ j (hj : j < kk.val), (w[j]).coeffs = F j)
    {n k' N : Usize} (polys : Std.Array (Std.Array U8 n) k') (h : k'.val * n.val = N.val)
    (hn : n.val = 32 * d) (hN : N.val = 32 * d * kk.val)
    (hp : ∀ j < kk.val, ∀ t (ht : t < 32 * d),
      UInt8.ofBitVec ((polys.val[j]!).val[t]!).bv = (ByteEncode d (F j) hd)[t]) :
    ∀ i (hi : i < 32 * d * kk.val),
      (arrayToBytes (Model.flatten polys h))[i]'(by omega) = (PolyVector.ByteEncode d w hd)[i] := by
  intro i hi
  have hd0 : 0 < 32 * d := by omega
  rw [PolyVector.ByteEncode_getElem d w hd i hi, arrayToBytes_getElem _ _ (by omega),
    flatten_getElem! _ _ _ (by omega), hn, hw _ (Nat.div_lt_of_lt_mul hi)]
  exact hp _ (Nat.div_lt_of_lt_mul hi) _ (Nat.mod_lt _ hd0)

theorem ntt_vec_encode_glue {kk : K} (w : NTTVector kk)
    (F : ℕ → Vector (ZMod q) 256) (hw : ∀ j (hj : j < kk.val), (w[j]).coeffs = F j)
    {n k' N : Usize} (polys : Std.Array (Std.Array U8 n) k') (h : k'.val * n.val = N.val)
    (hn : n.val = 384) (hN : N.val = 384 * kk.val)
    (hp : ∀ j < kk.val, ∀ t (ht : t < 384),
      UInt8.ofBitVec ((polys.val[j]!).val[t]!).bv = (ByteEncode 12 (F j))[t]) :
    ∀ i (hi : i < 384 * kk.val),
      (arrayToBytes (Model.flatten polys h))[i]'(by omega) = (ByteEncode₁₂ w)[i] := by
  intro i hi
  rw [ByteEncode₁₂_getElem w i hi, arrayToBytes_getElem _ _ (by omega),
    flatten_getElem! _ _ _ (by omega), hn, hw _ (Nat.div_lt_of_lt_mul hi)]
  exact hp _ (Nat.div_lt_of_lt_mul hi) _ (Nat.mod_lt _ (by norm_num))

def chunkBytes {N : Usize} (enc : Std.Array U8 N) (n j : ℕ) : ByteVec n :=
  Vector.ofFn fun t => UInt8.ofBitVec (enc.val[n * j + t.val]!).bv

theorem chunk_eq {n N : Usize} (x : Std.Array U8 n) (enc : Std.Array U8 N) (nn j : ℕ) (hn : n.val = nn)
    (hx : ∀ t < nn, x.val[t]! = enc.val[nn * j + t]!) (t : ℕ) (ht : t < nn) :
    (arrayToBytes x)[t]'(by omega) = (chunkBytes enc nn j)[t] := by
  rw [arrayToBytes_getElem _ _ (by omega), hx t ht]
  simp [chunkBytes]

theorem chunk_slice {N : Usize} (enc : Std.Array U8 N) (nn kk : ℕ) (B : ByteVec (nn * kk))
    (hB : ∀ t (ht : t < nn * kk), B[t] = UInt8.ofBitVec (enc.val[t]!).bv) (j : ℕ) (hj : j < kk) :
    chunkBytes enc nn j = Wychelean.slice B (nn * j) nn (by
      have := Nat.mul_le_mul_left nn (show j + 1 ≤ kk by omega); rw [Nat.mul_succ] at this; omega) := by
  apply Vector.ext; intro t ht
  have h1 : nn * j + t < nn * kk := by
    have := Nat.mul_le_mul_left nn (show j + 1 ≤ kk by omega); rw [Nat.mul_succ] at this; omega
  simp only [chunkBytes, Wychelean.slice, Vector.getElem_ofFn]
  rw [hB _ h1]

theorem vec_decode_glue (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 12) {kk : K} {N : Usize} (enc : Std.Array U8 N)
    (B : ByteVec (32 * d * kk)) (hB : ∀ t (ht : t < 32 * d * kk), B[t] = UInt8.ofBitVec (enc.val[t]!).bv)
    (w : PolyVector (m d) kk) (F : ℕ → Vector (ZMod (m d)) 256)
    (hw : ∀ j (hj : j < kk.val), (w[j]).coeffs = F j)
    (hp : ∀ j < kk.val, F j = ByteDecode (chunkBytes enc (32 * d) j) hd) :
    w = PolyVector.ByteDecode d B hd := by
  apply Vector.ext; intro j hj
  simp only [PolyVector.ByteDecode, Vector.getElem_ofFn]
  have e : ∀ p : Wychelean.KEM.MLKEM.Polynomial (m d), p = ⟨p.coeffs⟩ := fun p => rfl
  rw [e w[j], hw j hj, hp j hj, chunk_slice enc (32 * d) kk B hB j hj]

theorem ntt_vec_decode_glue {kk : K} {N : Usize} (enc : Std.Array U8 N)
    (B : ByteVec (384 * kk.val)) (hB : ∀ t (ht : t < 384 * kk.val), B[t] = UInt8.ofBitVec (enc.val[t]!).bv)
    (w : NTTVector kk) (F : ℕ → Vector (ZMod q) 256)
    (hw : ∀ j (hj : j < kk.val), (w[j]).coeffs = F j)
    (hp : ∀ j < kk.val, F j = ByteDecode (d := 12) (chunkBytes enc 384 j)) :
    w = ByteDecode₁₂ B := by
  apply Vector.ext; intro j hj
  simp only [ByteDecode₁₂, Vector.getElem_ofFn]
  have e : ∀ p : Tq, p = ⟨p.coeffs⟩ := fun p => rfl
  rw [e w[j], hw j hj, hp j hj]
  exact congrArg (fun x => Tq.mk (ByteDecode (d := 12) x)) (chunk_slice enc 384 kk B hB j hj)

@[step] theorem from_slice_320_spec (s : Slice U8) (h : s.val.length = 320) :
    hybrid_array.Array_u8_U320.from_slice_u8_U320U8U320 s ⦃ x => x.val = s.val ⦄ := by
  simp [hybrid_array.Array_u8_U320.from_slice_u8_U320U8U320, h]

@[step] theorem from_slice_352_spec (s : Slice U8) (h : s.val.length = 352) :
    hybrid_array.Array_u8_U352.from_slice_u8_U352U8U352 s ⦃ x => x.val = s.val ⦄ := by
  simp [hybrid_array.Array_u8_U352.from_slice_u8_U352U8U352, h]

@[step] theorem from_slice_384_spec (s : Slice U8) (h : s.val.length = 384) :
    hybrid_array.Array_u8_U384.from_slice_u8_U384U8U384 s ⦃ x => x.val = s.val ⦄ := by
  simp [hybrid_array.Array_u8_U384.from_slice_u8_U384U8U384, h]

@[step] theorem subslice_640_spec (a : Std.Array U8 640#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 640) :
    hybrid_array.Array_u8_U640_Index_Range_usize.index_u8_Range_usize_U640U8RangeUsizeU640 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U640_Index_Range_usize.index_u8_Range_usize_U640U8RangeUsizeU640
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

@[step] theorem subslice_960_spec (a : Std.Array U8 960#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 960) :
    hybrid_array.Array_u8_U960_Index_Range_usize.index_u8_Range_usize_U960U8RangeUsizeU960 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U960_Index_Range_usize.index_u8_Range_usize_U960U8RangeUsizeU960
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

@[step] theorem subslice_1408_spec (a : Std.Array U8 1408#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 1408) :
    hybrid_array.Array_u8_U1408_Index_Range_usize.index_u8_Range_usize_U1408U8RangeUsizeU1408 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U1408_Index_Range_usize.index_u8_Range_usize_U1408U8RangeUsizeU1408
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

@[step] theorem subslice_768_spec (a : Std.Array U8 768#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 768) :
    hybrid_array.Array_u8_U768_Index_Range_usize.index_u8_Range_usize_U768U8RangeUsizeU768 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U768_Index_Range_usize.index_u8_Range_usize_U768U8RangeUsizeU768
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

@[step] theorem subslice_1152_spec (a : Std.Array U8 1152#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 1152) :
    hybrid_array.Array_u8_U1152_Index_Range_usize.index_u8_Range_usize_U1152U8RangeUsizeU1152 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U1152_Index_Range_usize.index_u8_Range_usize_U1152U8RangeUsizeU1152
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

@[step] theorem subslice_1536_spec (a : Std.Array U8 1536#usize) (r : core.ops.range.Range Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ 1536) :
    hybrid_array.Array_u8_U1536_Index_Range_usize.index_u8_Range_usize_U1536U8RangeUsizeU1536 a r
      ⦃ s => s.val.length = r.end.val - r.start.val ∧
        ∀ t, t + r.start.val < r.end.val → s.val[t]! = a.val[r.start.val + t]! ⦄ := by
  unfold hybrid_array.Array_u8_U1536_Index_Range_usize.index_u8_Range_usize_U1536U8RangeUsizeU1536
  let* ⟨ s, hs1, hs2 ⟩ ← Slice.subslice_spec
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hs1]; simp [List.slice_length]; omega
  · have := hs2 t ht
    simpa [Slice.getElem!_Nat_eq] using this

theorem vec_encode_10_2_loop_spec (iter : core.ops.range.Range Usize) (v : Vec2)
    (polys : Std.Array Bytes320 2#usize)
    (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2) (hv : Vec.Bounded (m 10) v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 10 (v.val[j]!.toVector (m 10))) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.encode_BaseField_U10_U2BaseFieldU10U2_loop iter v polys
      ⦃ (r : Std.Array Bytes320 2#usize) => ∀ j < 2,
        arrayToBytes (r.val[j]! : Bytes320) = ByteEncode 10 (v.val[j]!.toVector (m 10)) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U2_Encode_U10.encode_BaseField_U10_U2BaseFieldU10U2_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U2_Index_usize.index_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2,
      hybrid_array.Array_Array_u8_U320_U2_IndexMut_usize.index_mut_Array_u8_U320_usize_U2Array_u8_U320UsizeU2]
    step*
    · rw [pbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U320_usize_U2_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, pbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_10_2_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 640#usize)
    (n : Usize) (polys : Vec2)
    (hn : n.val = 320) (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded (m 10) polys.val[j]! ∧
      (polys.val[j]!).toVector (m 10) = ByteDecode (d := 10) (chunkBytes enc 320 j)) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.decode_BaseField_U10_U2BaseFieldU10U2_loop iter enc n polys
      ⦃ (r : Vec2) => ∀ j < 2, Coeffs.Bounded (m 10) r.val[j]! ∧
        (r.val[j]!).toVector (m 10) = ByteDecode (d := 10) (chunkBytes enc 320 j) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U2_Encode_U10.decode_BaseField_U10_U2BaseFieldU10U2_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U2_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U2Polynomial_BaseFieldUsizeU2]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_Polynomial_BaseField_usize_U2_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨pbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 320) = chunkBytes enc 320 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 320 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact pbf_post1.trans (congrArg (fun B => ByteDecode (d := 10) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_encode_10_3_loop_spec (iter : core.ops.range.Range Usize) (v : Vec3)
    (polys : Std.Array Bytes320 3#usize)
    (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3) (hv : Vec.Bounded (m 10) v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 10 (v.val[j]!.toVector (m 10))) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.encode_BaseField_U10_U3BaseFieldU10U3_loop iter v polys
      ⦃ (r : Std.Array Bytes320 3#usize) => ∀ j < 3,
        arrayToBytes (r.val[j]! : Bytes320) = ByteEncode 10 (v.val[j]!.toVector (m 10)) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U3_Encode_U10.encode_BaseField_U10_U3BaseFieldU10U3_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U3_Index_usize.index_Polynomial_BaseField_usize_U3Polynomial_BaseFieldUsizeU3,
      hybrid_array.Array_Array_u8_U320_U3_IndexMut_usize.index_mut_Array_u8_U320_usize_U3Array_u8_U320UsizeU3]
    step*
    · rw [pbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U320_usize_U3_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, pbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_10_3_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 960#usize)
    (n : Usize) (polys : Vec3)
    (hn : n.val = 320) (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded (m 10) polys.val[j]! ∧
      (polys.val[j]!).toVector (m 10) = ByteDecode (d := 10) (chunkBytes enc 320 j)) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.decode_BaseField_U10_U3BaseFieldU10U3_loop iter enc n polys
      ⦃ (r : Vec3) => ∀ j < 3, Coeffs.Bounded (m 10) r.val[j]! ∧
        (r.val[j]!).toVector (m 10) = ByteDecode (d := 10) (chunkBytes enc 320 j) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U3_Encode_U10.decode_BaseField_U10_U3BaseFieldU10U3_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U3_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U3Polynomial_BaseFieldUsizeU3]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_Polynomial_BaseField_usize_U3_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨pbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 320) = chunkBytes enc 320 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 320 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact pbf_post1.trans (congrArg (fun B => ByteDecode (d := 10) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_encode_11_4_loop_spec (iter : core.ops.range.Range Usize) (v : Vec4)
    (polys : Std.Array Bytes352 4#usize)
    (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4) (hv : Vec.Bounded (m 11) v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 11 (v.val[j]!.toVector (m 11))) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.encode_BaseField_U11_U4BaseFieldU11U4_loop iter v polys
      ⦃ (r : Std.Array Bytes352 4#usize) => ∀ j < 4,
        arrayToBytes (r.val[j]! : Bytes352) = ByteEncode 11 (v.val[j]!.toVector (m 11)) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U4_Encode_U11.encode_BaseField_U11_U4BaseFieldU11U4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U4_Index_usize.index_Polynomial_BaseField_usize_U4Polynomial_BaseFieldUsizeU4,
      hybrid_array.Array_Array_u8_U352_U4_IndexMut_usize.index_mut_Array_u8_U352_usize_U4Array_u8_U352UsizeU4]
    step*
    · rw [pbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U352_usize_U4_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, pbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_11_4_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 1408#usize)
    (n : Usize) (polys : Vec4)
    (hn : n.val = 352) (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded (m 11) polys.val[j]! ∧
      (polys.val[j]!).toVector (m 11) = ByteDecode (d := 11) (chunkBytes enc 352 j)) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.decode_BaseField_U11_U4BaseFieldU11U4_loop iter enc n polys
      ⦃ (r : Vec4) => ∀ j < 4, Coeffs.Bounded (m 11) r.val[j]! ∧
        (r.val[j]!).toVector (m 11) = ByteDecode (d := 11) (chunkBytes enc 352 j) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U4_Encode_U11.decode_BaseField_U11_U4BaseFieldU11U4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_Polynomial_BaseField_U4_IndexMut_usize.index_mut_Polynomial_BaseField_usize_U4Polynomial_BaseFieldUsizeU4]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_Polynomial_BaseField_usize_U4_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨pbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 352) = chunkBytes enc 352 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 352 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact pbf_post1.trans (congrArg (fun B => ByteDecode (d := 11) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_encode_ntt_12_2_loop_spec (iter : core.ops.range.Range Usize) (v : Vec2)
    (polys : Std.Array Bytes384 2#usize)
    (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2) (hv : Vec.Bounded q v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 12 (v.val[j]!.toVector q)) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.encode_BaseField_U12_U2BaseFieldU12U2_loop iter v polys
      ⦃ (r : Std.Array Bytes384 2#usize) => ∀ j < 2,
        arrayToBytes (r.val[j]! : Bytes384) = ByteEncode 12 (v.val[j]!.toVector q) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.encode_BaseField_U12_U2BaseFieldU12U2_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U2_Index_usize.index_NttPolynomial_BaseField_usize_U2NttPolynomial_BaseFieldUsizeU2,
      hybrid_array.Array_Array_u8_U384_U2_IndexMut_usize.index_mut_Array_u8_U384_usize_U2Array_u8_U384UsizeU2]
    step*
    · rw [npbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U384_usize_U2_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, npbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_ntt_12_2_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 768#usize)
    (n : Usize) (polys : Vec2)
    (hn : n.val = 384) (hend : iter.end.val = 2) (hst : iter.start.val ≤ 2)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded q polys.val[j]! ∧
      (polys.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j)) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.decode_BaseField_U12_U2BaseFieldU12U2_loop iter enc n polys
      ⦃ (r : Vec2) => ∀ j < 2, Coeffs.Bounded q r.val[j]! ∧
        (r.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.decode_BaseField_U12_U2BaseFieldU12U2_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U2_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U2NttPolynomial_BaseFieldUsizeU2]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_NttPolynomial_BaseField_usize_U2_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨npbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 384) = chunkBytes enc 384 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 384 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact npbf_post1.trans (congrArg (fun B => ByteDecode (d := 12) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_encode_ntt_12_3_loop_spec (iter : core.ops.range.Range Usize) (v : Vec3)
    (polys : Std.Array Bytes384 3#usize)
    (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3) (hv : Vec.Bounded q v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 12 (v.val[j]!.toVector q)) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.encode_BaseField_U12_U3BaseFieldU12U3_loop iter v polys
      ⦃ (r : Std.Array Bytes384 3#usize) => ∀ j < 3,
        arrayToBytes (r.val[j]! : Bytes384) = ByteEncode 12 (v.val[j]!.toVector q) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.encode_BaseField_U12_U3BaseFieldU12U3_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U3_Index_usize.index_NttPolynomial_BaseField_usize_U3NttPolynomial_BaseFieldUsizeU3,
      hybrid_array.Array_Array_u8_U384_U3_IndexMut_usize.index_mut_Array_u8_U384_usize_U3Array_u8_U384UsizeU3]
    step*
    · rw [npbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U384_usize_U3_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, npbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_ntt_12_3_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 1152#usize)
    (n : Usize) (polys : Vec3)
    (hn : n.val = 384) (hend : iter.end.val = 3) (hst : iter.start.val ≤ 3)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded q polys.val[j]! ∧
      (polys.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j)) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.decode_BaseField_U12_U3BaseFieldU12U3_loop iter enc n polys
      ⦃ (r : Vec3) => ∀ j < 3, Coeffs.Bounded q r.val[j]! ∧
        (r.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.decode_BaseField_U12_U3BaseFieldU12U3_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U3_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U3NttPolynomial_BaseFieldUsizeU3]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_NttPolynomial_BaseField_usize_U3_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨npbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 384) = chunkBytes enc 384 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 384 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact npbf_post1.trans (congrArg (fun B => ByteDecode (d := 12) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 3 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_encode_ntt_12_4_loop_spec (iter : core.ops.range.Range Usize) (v : Vec4)
    (polys : Std.Array Bytes384 4#usize)
    (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4) (hv : Vec.Bounded q v)
    (hinv : ∀ j < iter.start.val, arrayToBytes polys.val[j]! = ByteEncode 12 (v.val[j]!.toVector q)) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.encode_BaseField_U12_U4BaseFieldU12U4_loop iter v polys
      ⦃ (r : Std.Array Bytes384 4#usize) => ∀ j < 4,
        arrayToBytes (r.val[j]! : Bytes384) = ByteEncode 12 (v.val[j]!.toVector q) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.encode_BaseField_U12_U4BaseFieldU12U4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U4_Index_usize.index_NttPolynomial_BaseField_usize_U4NttPolynomial_BaseFieldUsizeU4,
      hybrid_array.Array_Array_u8_U384_U4_IndexMut_usize.index_mut_Array_u8_U384_usize_U4Array_u8_U384UsizeU4]
    step*
    · rw [npbf_post]; exact hv _ (List.getElem_mem _)
    · intro j hj
      rw [index_mut_Array_u8_U384_usize_U4_back_post, array_set_getElem!]
      split
      · rename_i hj'
        rw [auu_post, npbf_post, hj'.1, getElem!_pos]
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

theorem vec_decode_ntt_12_4_loop_spec (iter : core.ops.range.Range Usize) (enc : Std.Array U8 1536#usize)
    (n : Usize) (polys : Vec4)
    (hn : n.val = 384) (hend : iter.end.val = 4) (hst : iter.start.val ≤ 4)
    (hinv : ∀ j < iter.start.val, Coeffs.Bounded q polys.val[j]! ∧
      (polys.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j)) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.decode_BaseField_U12_U4BaseFieldU12U4_loop iter enc n polys
      ⦃ (r : Vec4) => ∀ j < 4, Coeffs.Bounded q r.val[j]! ∧
        (r.val[j]!).toVector q = ByteDecode (d := 12) (chunkBytes enc 384 j) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.decode_BaseField_U12_U4BaseFieldU12U4_loop
  by_cases h : iter.start.val < iter.end.val
  · let* ⟨ o, iter1, ho, h1, h2 ⟩ ← range_next_some
    simp only [ho, hybrid_array.Array_NttPolynomial_BaseField_U4_IndexMut_usize.index_mut_NttPolynomial_BaseField_usize_U4NttPolynomial_BaseFieldUsizeU4]
    step*
    · rw [s_post, i3_post, i1_post, i2_post, hn, Nat.add_mul]; omega
    · intro j hj
      rw [index_mut_NttPolynomial_BaseField_usize_U4_back_post, array_set_getElem!]
      split
      · rename_i hj'
        refine ⟨npbf_post, ?_⟩
        have hxc : (arrayToBytes x : ByteVec 384) = chunkBytes enc 384 j := by
          apply Vector.ext; intro t ht
          refine chunk_eq x enc 384 j rfl (fun t' ht' => ?_) t ht
          rw [x_post, s_post1 t' (by rw [i1_post, i3_post, i2_post, hn, Nat.add_mul]; omega),
            i1_post, hn, hj'.1, Nat.mul_comm]
        exact npbf_post1.trans (congrArg (fun B => ByteDecode (d := 12) B) hxc)
      · exact hinv j (by rename_i hj'; simp at hj'; omega)
  · let* ⟨ o, iter1, ho, h1 ⟩ ← range_next_none
    simp only [ho, WP.spec_ok]
    intro j hj
    exact hinv j (by omega)
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

-- INTERFACE
@[step] theorem vec_encode_spec_2 (v : Vec2)
    (hv : Vec.Bounded (m 10) v) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.encode_BaseField_U10_U2BaseFieldU10U2 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_512) 10 (toPolyVec (m 10) v) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U2_Encode_U10.encode_BaseField_U10_U2BaseFieldU10U2
  simp only [hybrid_array.Array_Array_u8_U320_U2_Default.default_Array_u8_U320_U2Array_u8_U320U2,
    hybrid_array.Array_Array_u8_U320_U2_Deref.deref_Array_u8_U320_U2Array_u8_U320U2,
    core.slice.SliceArray_u8_U320.lenArray_u8_U320,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U10_VectorEncodingSize_U2.flatten_U10_U2U10U2,
    hybrid_array.flatten.Array_Array_u8_U320_U2_Flatten_u8_U640.flatten_u8_U2_U320U8U2U320]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_10_2_loop_spec
  apply Vector.ext; intro i hi
  exact vec_encode_glue 10 _ (kk := k .ML_KEM_512) (toPolyVec (m 10) v) (fun j => (v.val[j]!).toVector (m 10))
    (fun j hj => toPolyVec_coeffs (m 10) v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem vec_decode_spec_2 (b : Std.Array U8 640#usize) :
    module_lattice.encoding.Vector_BaseField_U2_Encode_U10.decode_BaseField_U10_U2BaseFieldU10U2 b
      ⦃ r => Vec.Bounded (m 10) r ∧ toPolyVec (m 10) r = PolyVector.ByteDecode (k := k .ML_KEM_512) 10 (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U2_Encode_U10.decode_BaseField_U10_U2BaseFieldU10U2
  simp only [typenum.uint.U320_Unsigned.USIZE_U320U160B0,
    hybrid_array.Array_Polynomial_BaseField_U2_Default.default_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    hybrid_array.Array_Polynomial_BaseField_U2_Deref.deref_Polynomial_BaseField_U2Polynomial_BaseFieldU2,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_10_2_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact vec_decode_glue 10 _ (kk := k .ML_KEM_512) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toPolyVec (m 10) r)
      (fun j => Coeffs.toVector (m 10) (r.val[j]!)) (fun j hj => toPolyVec_coeffs (m 10) r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem vec_encode_spec_3 (v : Vec3)
    (hv : Vec.Bounded (m 10) v) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.encode_BaseField_U10_U3BaseFieldU10U3 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_768) 10 (toPolyVec (m 10) v) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U3_Encode_U10.encode_BaseField_U10_U3BaseFieldU10U3
  simp only [hybrid_array.Array_Array_u8_U320_U3_Default.default_Array_u8_U320_U3Array_u8_U320U3,
    hybrid_array.Array_Array_u8_U320_U3_Deref.deref_Array_u8_U320_U3Array_u8_U320U3,
    core.slice.SliceArray_u8_U320.lenArray_u8_U320,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U10_VectorEncodingSize_U3.flatten_U10_U3U10U3,
    hybrid_array.flatten.Array_Array_u8_U320_U3_Flatten_u8_U960.flatten_u8_U3_U320U8U3U320]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_10_3_loop_spec
  apply Vector.ext; intro i hi
  exact vec_encode_glue 10 _ (kk := k .ML_KEM_768) (toPolyVec (m 10) v) (fun j => (v.val[j]!).toVector (m 10))
    (fun j hj => toPolyVec_coeffs (m 10) v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem vec_decode_spec_3 (b : Std.Array U8 960#usize) :
    module_lattice.encoding.Vector_BaseField_U3_Encode_U10.decode_BaseField_U10_U3BaseFieldU10U3 b
      ⦃ r => Vec.Bounded (m 10) r ∧ toPolyVec (m 10) r = PolyVector.ByteDecode (k := k .ML_KEM_768) 10 (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U3_Encode_U10.decode_BaseField_U10_U3BaseFieldU10U3
  simp only [typenum.uint.U320_Unsigned.USIZE_U320U160B0,
    hybrid_array.Array_Polynomial_BaseField_U3_Default.default_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    hybrid_array.Array_Polynomial_BaseField_U3_Deref.deref_Polynomial_BaseField_U3Polynomial_BaseFieldU3,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_10_3_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact vec_decode_glue 10 _ (kk := k .ML_KEM_768) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toPolyVec (m 10) r)
      (fun j => Coeffs.toVector (m 10) (r.val[j]!)) (fun j hj => toPolyVec_coeffs (m 10) r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem vec_encode_spec_4 (v : Vec4)
    (hv : Vec.Bounded (m 11) v) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.encode_BaseField_U11_U4BaseFieldU11U4 v
      ⦃ r => arrayToBytes r = PolyVector.ByteEncode (k := k .ML_KEM_1024) 11 (toPolyVec (m 11) v) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U4_Encode_U11.encode_BaseField_U11_U4BaseFieldU11U4
  simp only [hybrid_array.Array_Array_u8_U352_U4_Default.default_Array_u8_U352_U4Array_u8_U352U4,
    hybrid_array.Array_Array_u8_U352_U4_Deref.deref_Array_u8_U352_U4Array_u8_U352U4,
    core.slice.SliceArray_u8_U352.lenArray_u8_U352,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U11_VectorEncodingSize_U4.flatten_U11_U4U11U4,
    hybrid_array.flatten.Array_Array_u8_U352_U4_Flatten_u8_U1408.flatten_u8_U4_U352U8U4U352]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_11_4_loop_spec
  apply Vector.ext; intro i hi
  exact vec_encode_glue 11 _ (kk := k .ML_KEM_1024) (toPolyVec (m 11) v) (fun j => (v.val[j]!).toVector (m 11))
    (fun j hj => toPolyVec_coeffs (m 11) v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem vec_decode_spec_4 (b : Std.Array U8 1408#usize) :
    module_lattice.encoding.Vector_BaseField_U4_Encode_U11.decode_BaseField_U11_U4BaseFieldU11U4 b
      ⦃ r => Vec.Bounded (m 11) r ∧ toPolyVec (m 11) r = PolyVector.ByteDecode (k := k .ML_KEM_1024) 11 (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.Vector_BaseField_U4_Encode_U11.decode_BaseField_U11_U4BaseFieldU11U4
  simp only [typenum.uint.U352_Unsigned.USIZE_U352U176B0,
    hybrid_array.Array_Polynomial_BaseField_U4_Default.default_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    hybrid_array.Array_Polynomial_BaseField_U4_Deref.deref_Polynomial_BaseField_U4Polynomial_BaseFieldU4,
    core.slice.SlicePolynomial_BaseField.lenPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_11_4_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact vec_decode_glue 11 _ (kk := k .ML_KEM_1024) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toPolyVec (m 11) r)
      (fun j => Coeffs.toVector (m 11) (r.val[j]!)) (fun j hj => toPolyVec_coeffs (m 11) r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.encode_BaseField_U12_U2BaseFieldU12U2 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_512) (toNTTVec v) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.encode_BaseField_U12_U2BaseFieldU12U2
  simp only [hybrid_array.Array_Array_u8_U384_U2_Default.default_Array_u8_U384_U2Array_u8_U384U2,
    hybrid_array.Array_Array_u8_U384_U2_Deref.deref_Array_u8_U384_U2Array_u8_U384U2,
    core.slice.SliceArray_u8_U384.lenArray_u8_U384,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U12_VectorEncodingSize_U2.flatten_U12_U2U12U2,
    hybrid_array.flatten.Array_Array_u8_U384_U2_Flatten_u8_U768.flatten_u8_U2_U384U8U2U384]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_ntt_12_2_loop_spec
  apply Vector.ext; intro i hi
  exact ntt_vec_encode_glue (kk := k .ML_KEM_512) (toNTTVec v) (fun j => (v.val[j]!).toVector q)
    (fun j hj => toNTTVec_coeffs v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_2 (b : Std.Array U8 768#usize) :
    module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.decode_BaseField_U12_U2BaseFieldU12U2 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_512) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U2_Encode_U12.decode_BaseField_U12_U2BaseFieldU12U2
  simp only [typenum.uint.U384_Unsigned.USIZE_U384U192B0,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Default.default_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    hybrid_array.Array_NttPolynomial_BaseField_U2_Deref.deref_NttPolynomial_BaseField_U2NttPolynomial_BaseFieldU2,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_ntt_12_2_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact ntt_vec_decode_glue (kk := k .ML_KEM_512) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toNTTVec r)
      (fun j => Coeffs.toVector q (r.val[j]!)) (fun j hj => toNTTVec_coeffs r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem encode_u12_spec_2 (v : Vec2)
    (hv : Vec.Bounded q v) :
    param.MlKem512_PkeParams.encode_u12_MlKem512MlKem512 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_512) (toNTTVec v) ⦄ := by
  unfold param.MlKem512_PkeParams.encode_u12_MlKem512MlKem512
  exact ntt_vec_encode_spec_2 v hv

-- INTERFACE
@[step] theorem decode_u12_spec_2 (b : Std.Array U8 768#usize) :
    param.MlKem512_PkeParams.decode_u12_MlKem512MlKem512 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_512) (arrayToBytes b) ⦄ := by
  unfold param.MlKem512_PkeParams.decode_u12_MlKem512MlKem512
  exact ntt_vec_decode_spec_2 b

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.encode_BaseField_U12_U3BaseFieldU12U3 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_768) (toNTTVec v) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.encode_BaseField_U12_U3BaseFieldU12U3
  simp only [hybrid_array.Array_Array_u8_U384_U3_Default.default_Array_u8_U384_U3Array_u8_U384U3,
    hybrid_array.Array_Array_u8_U384_U3_Deref.deref_Array_u8_U384_U3Array_u8_U384U3,
    core.slice.SliceArray_u8_U384.lenArray_u8_U384,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U12_VectorEncodingSize_U3.flatten_U12_U3U12U3,
    hybrid_array.flatten.Array_Array_u8_U384_U3_Flatten_u8_U1152.flatten_u8_U3_U384U8U3U384]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_ntt_12_3_loop_spec
  apply Vector.ext; intro i hi
  exact ntt_vec_encode_glue (kk := k .ML_KEM_768) (toNTTVec v) (fun j => (v.val[j]!).toVector q)
    (fun j hj => toNTTVec_coeffs v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_3 (b : Std.Array U8 1152#usize) :
    module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.decode_BaseField_U12_U3BaseFieldU12U3 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_768) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U3_Encode_U12.decode_BaseField_U12_U3BaseFieldU12U3
  simp only [typenum.uint.U384_Unsigned.USIZE_U384U192B0,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Default.default_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    hybrid_array.Array_NttPolynomial_BaseField_U3_Deref.deref_NttPolynomial_BaseField_U3NttPolynomial_BaseFieldU3,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_ntt_12_3_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact ntt_vec_decode_glue (kk := k .ML_KEM_768) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toNTTVec r)
      (fun j => Coeffs.toVector q (r.val[j]!)) (fun j hj => toNTTVec_coeffs r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem encode_u12_spec_3 (v : Vec3)
    (hv : Vec.Bounded q v) :
    param.MlKem768_PkeParams.encode_u12_MlKem768MlKem768 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_768) (toNTTVec v) ⦄ := by
  unfold param.MlKem768_PkeParams.encode_u12_MlKem768MlKem768
  exact ntt_vec_encode_spec_3 v hv

-- INTERFACE
@[step] theorem decode_u12_spec_3 (b : Std.Array U8 1152#usize) :
    param.MlKem768_PkeParams.decode_u12_MlKem768MlKem768 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_768) (arrayToBytes b) ⦄ := by
  unfold param.MlKem768_PkeParams.decode_u12_MlKem768MlKem768
  exact ntt_vec_decode_spec_3 b

-- INTERFACE
@[step] theorem ntt_vec_encode_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.encode_BaseField_U12_U4BaseFieldU12U4 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_1024) (toNTTVec v) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.encode_BaseField_U12_U4BaseFieldU12U4
  simp only [hybrid_array.Array_Array_u8_U384_U4_Default.default_Array_u8_U384_U4Array_u8_U384U4,
    hybrid_array.Array_Array_u8_U384_U4_Deref.deref_Array_u8_U384_U4Array_u8_U384U4,
    core.slice.SliceArray_u8_U384.lenArray_u8_U384,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter,
    module_lattice.encoding.U12_VectorEncodingSize_U4.flatten_U12_U4U12U4,
    hybrid_array.flatten.Array_Array_u8_U384_U4_Flatten_u8_U1536.flatten_u8_U4_U384U8U4U384]
  step*
  let* ⟨ polys1, hp ⟩ ← vec_encode_ntt_12_4_loop_spec
  apply Vector.ext; intro i hi
  exact ntt_vec_encode_glue (kk := k .ML_KEM_1024) (toNTTVec v) (fun j => (v.val[j]!).toVector q)
    (fun j hj => toNTTVec_coeffs v j hj) polys1 _ rfl rfl
    (fun j hj t ht => by rw [← arrayToBytes_getElem _ t (by simp; omega), hp j (by simpa using hj)]; rfl) i
    (by simpa using hi)

-- INTERFACE
@[step] theorem ntt_vec_decode_spec_4 (b : Std.Array U8 1536#usize) :
    module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.decode_BaseField_U12_U4BaseFieldU12U4 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_1024) (arrayToBytes b) ⦄ := by
  unfold module_lattice.encoding.NttVector_BaseField_U4_Encode_U12.decode_BaseField_U12_U4BaseFieldU12U4
  simp only [typenum.uint.U384_Unsigned.USIZE_U384U192B0,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Default.default_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    hybrid_array.Array_NttPolynomial_BaseField_U4_Deref.deref_NttPolynomial_BaseField_U4NttPolynomial_BaseFieldU4,
    core.slice.SliceNttPolynomial_BaseField.lenNttPolynomial_BaseField,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsCollectIntoIterator.into_iter]
  step*
  let* ⟨ r, hr ⟩ ← vec_decode_ntt_12_4_loop_spec
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [← getElem!_pos r.val j hj]
    exact (hr j (by simpa using hj)).1
  · exact ntt_vec_decode_glue (kk := k .ML_KEM_1024) b (arrayToBytes b)
      (fun t ht => arrayToBytes_getElem b t (by simpa using ht)) (toNTTVec r)
      (fun j => Coeffs.toVector q (r.val[j]!)) (fun j hj => toNTTVec_coeffs r j hj)
      (fun j hj => (hr j (by simpa using hj)).2)

-- INTERFACE
@[step] theorem encode_u12_spec_4 (v : Vec4)
    (hv : Vec.Bounded q v) :
    param.MlKem1024_PkeParams.encode_u12_MlKem1024MlKem1024 v
      ⦃ r => arrayToBytes r = ByteEncode₁₂ (k := k .ML_KEM_1024) (toNTTVec v) ⦄ := by
  unfold param.MlKem1024_PkeParams.encode_u12_MlKem1024MlKem1024
  exact ntt_vec_encode_spec_4 v hv

-- INTERFACE
@[step] theorem decode_u12_spec_4 (b : Std.Array U8 1536#usize) :
    param.MlKem1024_PkeParams.decode_u12_MlKem1024MlKem1024 b
      ⦃ r => Vec.Bounded q r ∧ toNTTVec r = ByteDecode₁₂ (k := k .ML_KEM_1024) (arrayToBytes b) ⦄ := by
  unfold param.MlKem1024_PkeParams.decode_u12_MlKem1024MlKem1024
  exact ntt_vec_decode_spec_4 b


end MlKem.Properties
