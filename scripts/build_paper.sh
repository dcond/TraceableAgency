#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
paper_dir="$repo_root/Paper"
mode="${1:---check}"
paper_version="${2:-v10}"

case "$mode" in
  --check|--update) ;;
  *)
    echo "usage: $0 [--check|--update] [v10|v11]" >&2
    exit 2
    ;;
esac

case "$paper_version" in
  v10) paper_epoch=1788307200 ;;
  v11) paper_epoch=1793664000 ;;
  *)
    echo "ERROR: unsupported paper version: $paper_version" >&2
    exit 2
    ;;
esac
paper_name="trace_tempered_choice_$paper_version"

build_dir="$(mktemp -d "${TMPDIR:-/tmp}/traceable-agency-paper.XXXXXX")"
trap 'rm -rf "$build_dir"' EXIT

export SOURCE_DATE_EPOCH="$paper_epoch"
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C

(
  cd "$paper_dir"
  # pdfTeX otherwise derives the trailer ID from the temporary output path.
  # Omitting that optional identifier makes clean builds byte-for-byte stable.
  latexmk -pdf -usepretex='\pdftrailerid{}' \
    -interaction=nonstopmode -halt-on-error -file-line-error \
    -outdir="$build_dir" "$paper_name.tex"
)

built_pdf="$build_dir/$paper_name.pdf"
tracked_pdf="$paper_dir/$paper_name.pdf"

if [[ "$mode" == "--update" ]]; then
  cp "$built_pdf" "$tracked_pdf"
  echo "updated $tracked_pdf"
elif ! cmp -s "$built_pdf" "$tracked_pdf"; then
  echo "ERROR: $tracked_pdf is not the reproducible build of $paper_name.tex" >&2
  exit 1
else
  echo "paper PDF matches the reproducible build"
fi
