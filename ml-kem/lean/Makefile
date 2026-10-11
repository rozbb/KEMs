# ML-KEM verification convenience targets.
#
# Run from this directory (ml-kem/lean). These wrap the `lake` invocations for the ML-KEM
# correspondence proofs. Extraction (Rust -> Lean) lives in `../extract_rust_to_lean.sh`, which
# regenerates `ExtractedRust/`; this file only builds/checks what is already extracted.

LAKE ?= lake

.DEFAULT_GOAL := help

# The extracted ExtractedRust/*.lean plus every MlKem/Properties/*.lean, then TopLevelTheorems.lean,
# which states the top-level results, and TrustBase.lean, which re-checks their axiom footprint
# against the audited list. A green build IS the machine-checked proof.
.PHONY: prove-mlkem
prove-mlkem:
	$(LAKE) build MlKem TopLevelTheorems TrustBase

.PHONY: help
help:
	@echo "ML-KEM targets (run from ml-kem/lean):"
	@echo "  make prove-mlkem   the proofs and their trust base"
