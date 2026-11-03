#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if ! command -v rg >/dev/null 2>&1; then
  echo 'ERROR: ripgrep (rg) is required for source auditing; install it before running this check.' >&2
  exit 1
fi

./scripts/update_certificate_manifest.sh --check
python3 scripts/check_trust_dependencies.py
python3 scripts/check_trust_imports.py

if rg --hidden --no-ignore --glob '*.lean' '\bsorry\b|\badmit\b|\bnative_decide\b|implemented_by|\bextern\b|run_meta|opaqueDecl|addDecl(Core|WithoutChecking)?|mkSorry|sorryAx|debug\.skipKernelTC|unsafeCast|Lean\.trustCompiler' TraceableAgency TraceableAgency.lean; then
  echo 'ERROR: proof hole or prohibited unchecked mechanism' >&2
  exit 1
fi
if rg --hidden --no-ignore --glob '*.lean' '^\s*(private\s+)?axiom\s+[[:alnum:]_.'\''«»]+\s*[:({]' TraceableAgency TraceableAgency.lean; then
  echo 'ERROR: project axiom declaration' >&2
  exit 1
fi

# Remove only this project's generated outputs, preserving dependency caches.
# Every project source is then re-elaborated before inspecting proof bodies.
lake clean TraceableAgency
LAKE_ARTIFACT_CACHE=false lake build TraceableAgency.Audit.TrustBoundary

# No environment flag can skip this final kernel replay.
lake env leanchecker --fresh TraceableAgency.Audit.TrustBoundary
echo 'Complete trust-boundary certificate passed.'
