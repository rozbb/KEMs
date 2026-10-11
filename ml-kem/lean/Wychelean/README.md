# Wychelean (vendored)

This directory is vendored from [rozbb/wychelean](https://github.com/rozbb/wychelean) at commit
`93b26caa7075d503198d5ccb119052b79a56f7d4`. It contains the ML-KEM spec and the modules it
transitively depends on (Utils, Keccak, SHA3, and the MLKEM Properties). It is used under its
MIT / Apache-2.0 dual license (see `LICENSE-MIT` and `LICENSE-APACHE` in this directory).

Upstream targets Lean v4.34.0-rc2 with a newer mathlib. This copy is backported to Lean v4.31.0
and the mathlib version pinned by Aeneas. **No spec definitions were changed.** Every `def`,
`structure`, `abbrev`, `instance`, and theorem statement is identical to upstream. Only proof
scripts were edited, and one proof-only helper lemma was added:

- `Utils/Bytes.lean`: `ofBitsLE.testBit_go` base case. `simp [hb]` could not rewrite `v[lo]`
  here, so the case split on the bit is now done after a `simp only`.
- `Utils/Bits.lean`: `ofBitsLE_rotateLeft`. The older `BitVec.getLsbD_rotateLeft` gives a
  `bif`/`cond`, which `split` cannot handle, so the proof uses `by_cases` plus `cond_true`/`cond_false`.
- `Hashes/SHA3/XOF/Properties.lean`: `dite_eq_left h`/`dite_eq_right h` are missing from the
  older core. They are replaced by the equivalent `dif_pos h`/`dif_neg h`.
- `KEM/MLKEM/Properties/Loops.lean`:
  - `Fin.foldl 0 f a` does not reduce to `a` by `rfl`, so the proofs now use `Fin.foldl_zero`.
  - `dite_eq_left_of_eq_true (eq_true h)` is replaced by `dif_pos h`.
  - In Lean 4.31, `do` blocks thread several `let mut` variables through `MProd` rather than
    `Prod`. A proof-only helper lemma `foldl_mprod_prod` was added, and the `NTT_eq_forward`/
    `NTTInv_eq_inverse` proofs use it to move those folds over to `Prod`.
