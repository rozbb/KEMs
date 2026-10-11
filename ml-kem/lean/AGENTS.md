# Before modifying proofs

* Read the ML-KEM specification in `Wychelean/KEM/MLKEM/` (FIPS 203)

# When modifying proofs

* Do NOT modify `TopLevelTheorems.lean` unless it's absolutely necessary, or you were explicitly asked to. And if you do modify it, highlight it in your summary to your human.
* Ditto for `TrustBase.lean`
* Do NOT modify `Wychelean/` except to keep it building; it's the spec, vendored from upstream. If you must, only touch proofs, and list the change in `Wychelean/README.md`.

# When modifying `TopLevelTheorems.lean` or `TrustBase.lean`

* Modify as few things as possible
* If you must write prose, write it using the style of the rest of the file
* Keep all proofs to one line, moving proof bodies into other files as needed
