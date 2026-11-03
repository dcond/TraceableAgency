#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

./scripts/update_certificate_manifest.sh --check

if rg --glob '*.lean' '\bsorry\b|\badmit\b|run_meta|opaqueDecl|addDecl(Core|WithoutChecking)?|mkSorry|sorryAx|debug\.skipKernelTC|unsafeCast|Lean\.trustCompiler' TraceableAgency; then
  echo 'ERROR: unchecked proof or prohibited kernel bypass' >&2
  exit 1
fi
if rg --glob '*.lean' '^\s*(private\s+)?axiom\s+[[:alnum:]_.'\''«»]+\s*[:({]' TraceableAgency; then
  echo 'ERROR: project mathematical axiom' >&2
  exit 1
fi

lake build TraceableAgency
lake build TraceableAgency.Section4.Audit TraceableAgency.Section3.Audit
lake build TraceableAgency.Theorem1.MaterialCalibration.RepresentationAudit
lake build TraceableAgency.Theorem1.Proof TraceableAgency.Audit.Axioms
lake env leanchecker --fresh TraceableAgency.Section4.Audit

echo 'Section 4 certificate passed.'
