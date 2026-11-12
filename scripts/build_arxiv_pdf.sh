#!/usr/bin/env bash
# Regenerate arxiv.tex (Palomar-archive appendix, PNG figures), compile DomainTheory.pdf.
# CMU-CS-TR deliverable only — no view.pdf / Zenodo copy, no arXiv zip unless --zip.
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="DomainTheory.pdf"
JOB="DomainTheory"
DO_ZIP=0

if [[ "${1:-}" == "--zip" ]]; then
  DO_ZIP=1
  shift
fi

# shellcheck source=scripts/pdf_checks.sh
source "$(dirname "$0")/pdf_checks.sh"

pdf_valid() {
  local f="$1"
  [[ -f "$f" ]] || return 1
  pdfinfo "$f" >/dev/null 2>&1 || return 1
  local pages
  pages="$(pdfinfo "$f" 2>/dev/null | awk '/^Pages:/ {print $2}')"
  [[ -n "$pages" && "$pages" -gt 0 ]]
}

compile_tex() {
  local target="$1"
  local clean="${2:-0}"
  if [[ "$clean" -eq 1 ]]; then
    latexmk -C -jobname="$JOB" "$target" >/dev/null 2>&1 || true
    rm -f "${JOB}.aux" "${JOB}.out" "${JOB}.toc" "${JOB}.lof" "${JOB}.bbl" "${JOB}.blg"
  fi
  latexmk -pdf -jobname="$JOB" -interaction=nonstopmode -halt-on-error "$target" >/dev/null 2>&1 || {
    echo "latexmk reported errors compiling ${target} → ${PDF}; tail of log:" >&2
    tail -n 40 "${JOB}.log" >&2 || true
    exit 1
  }
}

echo "==> Regenerating arxiv.tex + lean-listings/ + figures/ (Palomar-archive appendix)"
if [[ "${1:-}" == "--pdf-only" ]]; then
  echo "    (--pdf-only: skipping markdown/tex regeneration)"
else
  bash scripts/build_arxiv_tex.sh
fi

echo "==> Compiling ${PDF} (pdfLaTeX; see .latexmkrc)"
need_main=1
if pdf_valid "$PDF" \
  && [[ ! "$TEX" -nt "$PDF" ]] \
  && [[ ! arxiv.md -nt "$PDF" ]] \
  && [[ ! arxiv_with_code.md -nt "$PDF" ]] \
  && [[ ! lean-listings -nt "$PDF" ]] \
  && [[ ! figures -nt "$PDF" ]]; then
  need_main=0
fi
if [[ "$need_main" -eq 0 ]]; then
  echo "==> Reusing cached $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; arxiv.tex unchanged)"
else
  start_main=$(date +%s)
  main_clean=0
  if ! pdf_valid "$PDF"; then
    main_clean=1
  fi
  compile_tex "$TEX" "$main_clean"
  end_main=$(date +%s)
  main_secs=$((end_main - start_main))
  if ! pdf_valid "$PDF"; then
    echo "error: ${PDF} missing or corrupt after compile" >&2
    exit 1
  fi
  echo "wrote $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; compile ${main_secs}s)"
fi

# Drop legacy Zenodo / view.pdf alias if present.
rm -f view.pdf

echo "==> Font embedding check"
check_pdf_fonts_embedded "$PDF" "$PDF"

if [[ "$DO_ZIP" -eq 1 ]]; then
  echo "==> Packaging arXiv submission zip (--zip)"
  bash scripts/package_arxiv_submit.sh --skip-tex-build
fi
