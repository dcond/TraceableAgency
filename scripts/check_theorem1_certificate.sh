#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "== Lean/Lake versions =="
lake --version
lean_version="$(lake env lean --version)"
echo "$lean_version"
if [[ "$lean_version" != "Lean (version 4.32.1,"* ]]; then
  echo "ERROR: Theorem 1 certificate requires the pinned Lean 4.32.1 kernel."
  exit 1
fi

echo
echo "== Certificate artifact manifest =="
if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c Theorem1Verification/CERTIFICATE_SHA256SUMS
elif command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c Theorem1Verification/CERTIFICATE_SHA256SUMS
else
  echo "ERROR: neither shasum nor sha256sum is available."
  exit 1
fi

lean_sources=(
  TraceableAgency
  Theorem1Verification
  TraceableAgency.lean
  Theorem1Verification.lean
)

echo
echo "== Kernel-soundness source gate =="
if rg --glob '*.lean' \
  "run_meta|opaqueDecl|addDecl(Core|WithoutChecking)?|mkSorry|sorryAx|debug\\.skipKernelTC|unsafeCast|Lean\\.trustCompiler" \
  "${lean_sources[@]}"; then
  echo "ERROR: found a prohibited declaration-construction or kernel-bypass primitive."
  exit 1
fi

echo
echo "== Source hygiene =="
if rg --glob '*.lean' '\bsorry\b' "${lean_sources[@]}"; then
  echo "ERROR: found 'sorry' in Lean source."
  exit 1
fi
if rg --glob '*.lean' '\badmit\b' "${lean_sources[@]}"; then
  echo "ERROR: found 'admit' in Lean source."
  exit 1
fi
if rg --glob '*.lean' '^\s*axiom\s+[A-Za-z_][A-Za-z0-9_'"'"']*\s*[:({]' \
  "${lean_sources[@]}"; then
  echo "ERROR: found a declaration-level project axiom."
  exit 1
fi
if rg --glob '*.lean' '^\s*opaque\s+[A-Za-z_][A-Za-z0-9_'"'"']*\s*[:({]' \
  "${lean_sources[@]}"; then
  echo "ERROR: found a bare opaque declaration."
  exit 1
fi

echo
echo "== Building exact Theorem 1 target and audits =="
lake build Theorem1Verification

check_dir="$(mktemp -d "${TMPDIR:-/tmp}/theorem1_certificate_check.XXXXXX")"
check_file="$check_dir/Check.lean"
trap 'rm -f "$check_file"; rmdir "$check_dir"' EXIT
cat > "$check_file" <<'LEAN'
import Theorem1Verification

open TraceTemperedChoiceVerification

#check trace_tempered_choice_v3_theorem1
#print Theorem1Statement
#print TraceTemperedAxioms
#print A1_WeakOrder
#print A2_Continuity
#print A3_BlockComparisonCoherence
#print A4_RecordDataProcessing
#print A5_ActionDataProcessing
#print A6_BranchwiseContinuationConsistency
#print A7_MaterialRelevance
#print A8_PositiveTraceOrientation
#print WithinChannelRepresentation
#print SameWitnessBlockRepresentation
#print axioms TraceableAgency.GenericFaddeev.provedClassicalFaddeevTheoremAssumptions
#print axioms TraceableAgency.provedMainCharacterizationWithMoreover
#print axioms trace_tempered_choice_v3_theorem1
LEAN

echo
echo "== Checking public statement surface =="
lake env lean "$check_file"

echo
echo "== Fresh independent kernel replay =="
lake env leanchecker --fresh Theorem1Verification.Proof

echo "Theorem 1 verification certificate passed."
