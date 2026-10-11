#!/bin/bash

set -eux

REPO_ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "${REPO_ROOT}"

# The aeneas version we use is dictated by AENEAS_VERSION.txt in the crate root
AENEAS_VERSION="$(tr -d '[:space:]' < "${REPO_ROOT}/AENEAS_VERSION.txt")"
# Place to save aeneas and charon prebuilt binaries
BIN_DIR="${REPO_ROOT}/.aeneas-bin/${AENEAS_VERSION}"

# Fetch the appropriate aeneas/charon prebuilt binaries from Github, and cache them locally
case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)               AENEAS_ASSET="aeneas-linux-x86_64.tar.gz" ;;
    Linux-aarch64 | Linux-arm64) AENEAS_ASSET="aeneas-linux-aarch64.tar.gz" ;;
    Darwin-arm64)               AENEAS_ASSET="aeneas-macos-aarch64.tar.gz" ;;
    Darwin-x86_64)              AENEAS_ASSET="aeneas-macos-x86_64.tar.gz" ;;
    *)
        echo "No prebuilt aeneas for $(uname -s)-$(uname -m)." >&2
        echo "Upstream publishes linux-{x86_64,aarch64} and macos-{x86_64,aarch64}." >&2
        exit 1
        ;;
esac
if [ ! -x "${BIN_DIR}/aeneas" ] || [ ! -x "${BIN_DIR}/charon" ]; then
    rm -rf "${BIN_DIR}"
    mkdir -p "${BIN_DIR}"
    echo "Fetching aeneas binary from Github..."
    curl -fsSL --retry 3 \
        "https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_VERSION}/${AENEAS_ASSET}" \
        | tar xz -C "${BIN_DIR}"
fi

CHARON="${BIN_DIR}/charon"
AENEAS="${BIN_DIR}/aeneas"

# We don't want Charon's build artifacts to interfere with other builds, and
# vice-versa. So we give it its own directory
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${REPO_ROOT}/../target/charon}"
# Cargo doesn't know about the LLBC output, so it would skip Charon on an unchanged crate
cargo clean -q -p ml-kem
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "${WORK_DIR}"' EXIT

# ml-kem is generic over its parameter sets using typenum, which neither Charon nor Aeneas handle
# well generically. So we have Charon monomorphize everything reachable from the `aeneas_entry`
# module (`--cfg aeneas`), one copy per parameter set. We also extract module-lattice, which we
# verify rather than axiomatize.
RUSTFLAGS='--cfg aeneas' $CHARON cargo --preset=aeneas --monomorphize --no-dedup-serialized-ast \
    --start-from 'crate::aeneas_entry' --include module_lattice \
    --dest-file "${WORK_DIR}/mono.llbc" -- --no-default-features

# Aeneas doesn't support monomorphized crates out of the box. lean/scripts/fix_llbc.py patches the
# LLBC up, using some generic declarations it takes from a (small) non-monomorphized extraction.
cargo clean -q -p ml-kem
$CHARON cargo --preset=aeneas --no-dedup-serialized-ast \
    --start-from 'crate::pke' --opaque typenum --opaque hybrid_array \
    --dest-file "${WORK_DIR}/generic.llbc" -- --no-default-features
python3 lean/scripts/fix_llbc.py "${WORK_DIR}/mono.llbc" "${WORK_DIR}/generic.llbc" \
    "${WORK_DIR}/ExtractedRust.llbc"

# Extract to lean/ExtractedRust/{Types,Funs}.lean. The external definitions they use are in the
# hand-written lean/ExtractedRust/{Types,Funs}External.lean; Aeneas regenerates the templates for
# these, so that changes to the expected signatures show up in the diff.
$AENEAS "${WORK_DIR}/ExtractedRust.llbc" -backend lean -loops-to-rec -split-files \
    -namespace RustMlKem -dest "${WORK_DIR}/out"
mkdir -p lean/ExtractedRust
for f in Types Funs TypesExternal_Template FunsExternal_Template; do
    mv "${WORK_DIR}/out/${f}.lean" "lean/ExtractedRust/${f}.lean"
done
