#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

manifest="Certificate/SHA256SUMS"
mode="${1:---update}"

case "$mode" in
  --check|--update) ;;
  *)
    echo "usage: $0 [--check|--update]" >&2
    exit 2
    ;;
esac

if command -v shasum >/dev/null 2>&1; then
  hash_file() { shasum -a 256 "$1"; }
elif command -v sha256sum >/dev/null 2>&1; then
  hash_file() { sha256sum "$1"; }
else
  echo "ERROR: neither shasum nor sha256sum is available" >&2
  exit 1
fi

temp_manifest="$(mktemp "${TMPDIR:-/tmp}/traceable-agency-manifest.XXXXXX")"
temp_paths="$(mktemp "${TMPDIR:-/tmp}/traceable-agency-paths.XXXXXX")"
trap 'rm -f "$temp_manifest" "$temp_paths"' EXIT

git ls-files --cached --others --exclude-standard \
  | LC_ALL=C sort \
  | while IFS= read -r path; do
      [[ "$path" == "$manifest" ]] && continue
      [[ -f "$path" ]] || continue
      printf '%s\n' "$path"
    done > "$temp_paths"

while IFS= read -r path; do
  hash_file "$path"
done < "$temp_paths" > "$temp_manifest"

if [[ "$mode" == "--update" ]]; then
  cp "$temp_manifest" "$manifest"
  echo "updated $manifest ($(wc -l < "$manifest" | tr -d ' ') files)"
elif ! cmp -s "$temp_manifest" "$manifest"; then
  echo "ERROR: $manifest is stale or does not cover every repository file" >&2
  diff -u "$manifest" "$temp_manifest" || true
  exit 1
else
  echo "certificate manifest covers every repository file"
fi
