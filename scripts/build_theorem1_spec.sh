#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

target="Certificate/THEOREM1_FORMAL_SPECIFICATION.md"
mode="${1:---check}"

case "$mode" in
  --check|--update) ;;
  *)
    echo "usage: $0 [--check|--update]" >&2
    exit 2
    ;;
esac

generated="$(mktemp "${TMPDIR:-/tmp}/theorem1-formal-specification.XXXXXX")"
trap 'rm -f "$generated"' EXIT

lake env lean TraceableAgency/Audit/Theorem1Spec.lean > "$generated"

if [[ "$mode" == "--update" ]]; then
  cp "$generated" "$target"
  echo "updated $target"
elif ! cmp -s "$generated" "$target"; then
  echo "ERROR: $target is stale" >&2
  echo "Regenerate it with ./scripts/build_theorem1_spec.sh --update" >&2
  diff -u "$target" "$generated" || true
  exit 1
else
  echo "$target is current"
fi
