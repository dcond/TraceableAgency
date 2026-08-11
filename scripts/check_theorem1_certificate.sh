#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "== Pinned toolchain =="
lake --version
lake env lean --version

echo "== Complete byte manifest =="
./scripts/update_certificate_manifest.sh --check

echo "== Source hygiene =="
if rg --glob '*.lean' \
  'run_meta|opaqueDecl|addDecl(Core|WithoutChecking)?|mkSorry|sorryAx|debug\.skipKernelTC|unsafeCast|Lean\.trustCompiler' \
  TraceableAgency; then
  echo "ERROR: prohibited declaration construction or kernel bypass" >&2
  exit 1
fi
if rg --glob '*.lean' '\bsorry\b|\badmit\b' TraceableAgency; then
  echo "ERROR: unchecked proof hole" >&2
  exit 1
fi
if rg --glob '*.lean' \
  '^\s*(private\s+)?axiom\s+[[:alnum:]_.'\''«»]+\s*[:({]' \
  TraceableAgency; then
  echo "ERROR: declaration-level project axiom" >&2
  exit 1
fi

echo "== Minimal statement boundary =="
lake build TraceableAgency.Theorem1.Statements

echo "== Public proof and compatibility surface =="
lake build TraceableAgency
lake build TraceableAgency.PureTrace.Compatibility

echo "== Recursive kernel and dependency audits =="
lake build TraceableAgency.Audit

echo "== Reproducible paper =="
if [[ "${TRACEABLE_SKIP_PAPER_CHECK:-0}" == "1" ]]; then
  echo "paper was checked by the pinned TeX Live job"
else
  ./scripts/build_paper.sh --check
fi

echo "== Fresh kernel replay =="
if [[ "${TRACEABLE_SKIP_FRESH_CHECKER:-0}" == "1" ]]; then
  echo "fresh replay is reserved for the full local certificate"
else
  lake env leanchecker --fresh TraceableAgency.Theorem1.Proof
fi

echo "Theorem 1 certificate passed."
