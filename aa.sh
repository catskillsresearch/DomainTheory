#!/usr/bin/env bash
# Full local rebuild: notes → flattened md → scratch tex → PDF (+ optional --zip for default root).
# arxiv.tex and LaTeX aux files are ephemeral (see .gitignore); default keeps arxiv.pdf at repo root.
set -euo pipefail

INVOCATION_CWD="$(pwd)"
ROOT="$(cd "$(dirname "$0")" && pwd)"

SKIP_MERMAID=0
DO_ZIP=0
KEEP_SCRATCH=0
ROOT_MD=""

usage() {
  cat <<'EOF'
Usage: ./aa.sh [options] [ROOT.md]

  Regenerate dependency mermaid diagrams (default root only), flatten the note tree,
  build listings and figures, compile PDF in a scratch directory.

  With no ROOT.md, uses DomainTheory.md and writes arxiv.pdf + view.pdf at the
  repo root.

  With ROOT.md (absolute or relative to your shell cwd), flattens that tree and
  writes STEM.pdf in the directory where you invoked aa.sh (STEM = basename without .md).

Options:
  --zip            Package dist/arxiv_submit.zip (full DomainTheory.md build only)
  --skip-mermaid   Skip scripts/generate_dependency_mermaid.py --write
  --keep-scratch   Keep .build/aa/ scratch on success (for debugging failed pdflatex)
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --zip) DO_ZIP=1 ;;
    --skip-mermaid) SKIP_MERMAID=1 ;;
    --skip-zip)
      echo "note: --skip-zip is default; use --zip to build dist/arxiv_submit.zip" >&2
      ;;
    --keep-scratch) KEEP_SCRATCH=1 ;;
    -h | --help) usage; exit 0 ;;
    --) shift; break ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      if [[ -z "$ROOT_MD" ]]; then
        ROOT_MD="$1"
      else
        echo "unexpected extra argument: $1" >&2
        usage >&2
        exit 2
      fi
      ;;
  esac
  shift
done
while [[ $# -gt 0 ]]; do
  if [[ -z "$ROOT_MD" ]]; then
    ROOT_MD="$1"
  else
    echo "unexpected extra argument: $1" >&2
    exit 2
  fi
  shift
done

IS_DEFAULT=0
if [[ -z "$ROOT_MD" ]]; then
  ROOT_MD="${ROOT}/DomainTheory.md"
  IS_DEFAULT=1
else
  if [[ "$ROOT_MD" != /* ]]; then
    ROOT_MD="$(cd "$INVOCATION_CWD" && cd "$(dirname "$ROOT_MD")" && pwd)/$(basename "$ROOT_MD")"
  fi
  if [[ ! -f "$ROOT_MD" ]]; then
    echo "error: markdown root not found: $ROOT_MD" >&2
    exit 1
  fi
  case "$ROOT_MD" in
    "${ROOT}/DomainTheory.md") IS_DEFAULT=1 ;;
  esac
fi

STEM="$(basename "$ROOT_MD" .md)"
if [[ "$IS_DEFAULT" -eq 1 ]]; then
  BUILD="${ROOT}/.build/aa"
  PDF="${ROOT}/arxiv.pdf"
  VIEW="${ROOT}/view.pdf"
  TEX_BASENAME="arxiv.tex"
  export ARXIV_ROOT_MD="${ROOT}/DomainTheory.md"
  unset ARXIV_MD ARXIV_WITH_CODE ARXIV_TEX
else
  BUILD="${ROOT}/.build/aa/${STEM}"
  PDF="${INVOCATION_CWD}/${STEM}.pdf"
  TEX_BASENAME="${STEM}.tex"
  export ARXIV_ROOT_MD="$ROOT_MD"
  export ARXIV_MD="${BUILD}/flatten.md"
  export ARXIV_WITH_CODE="${BUILD}/with_code.md"
  export ARXIV_TEX="${BUILD}/${TEX_BASENAME}"
  DO_ZIP=0
fi

# shellcheck source=scripts/pdf_checks.sh
source "${ROOT}/scripts/pdf_checks.sh"

rm -rf "$BUILD"
mkdir -p "$BUILD"

cleanup() {
  if [[ "$IS_DEFAULT" -eq 1 ]]; then
    rm -f "${ROOT}/arxiv.tex"
    rm -f "${ROOT}"/arxiv.{aux,log,out,toc,lof,fls,fdb_latexmk,synctex.gz}
  fi
  if [[ "$KEEP_SCRATCH" -eq 0 ]]; then
    if [[ "$IS_DEFAULT" -eq 1 ]]; then
      rm -rf "${ROOT}/.build/aa"
    else
      rm -rf "$BUILD"
    fi
  fi
}

cd "$ROOT"

if [[ "$SKIP_MERMAID" -eq 0 && "$IS_DEFAULT" -eq 1 ]]; then
  echo "==> Regenerating dependency mermaid diagrams"
  python3 scripts/generate_dependency_mermaid.py --write
fi

echo "==> Building from $(basename "$ROOT_MD") (output: $(basename "$PDF"))"
bash scripts/build_arxiv_tex.sh

TEX_SRC="${ARXIV_TEX:-${ROOT}/arxiv.tex}"
if [[ ! -f "$TEX_SRC" ]]; then
  echo "error: build did not produce $TEX_SRC" >&2
  exit 1
fi

if [[ "$IS_DEFAULT" -eq 1 ]]; then
  mv "$TEX_SRC" "${BUILD}/arxiv.tex"
  TEX_COMPILE="${BUILD}/arxiv.tex"
else
  TEX_COMPILE="$TEX_SRC"
fi

ln -sf "${ROOT}/figures" "${BUILD}/figures"
ln -sf "${ROOT}/lean-listings" "${BUILD}/lean-listings"
export TEXINPUTS="${ROOT}//:${TEXINPUTS:-}"

rm -f "$PDF"
if [[ "$IS_DEFAULT" -eq 1 ]]; then
  rm -f "$VIEW"
fi

echo "==> Compiling $(basename "$PDF") (scratch tex: ${TEX_COMPILE})"
latexmk -C -cd "$TEX_COMPILE" >/dev/null 2>&1 || true
if ! latexmk -pdf -interaction=nonstopmode -halt-on-error -cd "$TEX_COMPILE"; then
  echo "pdflatex failed; log tail:" >&2
  tail -n 50 "$(dirname "$TEX_COMPILE")/$(basename "$TEX_COMPILE" .tex).log" >&2 || true
  echo "scratch kept at ${BUILD}/ (use --keep-scratch or fix and re-run)" >&2
  KEEP_SCRATCH=1
  exit 1
fi

SCRATCH_PDF="$(dirname "$TEX_COMPILE")/$(basename "$TEX_COMPILE" .tex).pdf"
if [[ ! -f "$SCRATCH_PDF" ]]; then
  echo "error: missing $SCRATCH_PDF after latexmk" >&2
  KEEP_SCRATCH=1
  exit 1
fi

cp -f "$SCRATCH_PDF" "$PDF"
echo "wrote $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages)"

if [[ "$IS_DEFAULT" -eq 1 ]]; then
  cp -f "$PDF" "$VIEW"
  echo "wrote view.pdf"
fi

echo "==> Font embedding check"
check_pdf_fonts_embedded "$PDF" "$(basename "$PDF")"

if [[ "$DO_ZIP" -eq 1 && "$IS_DEFAULT" -eq 1 ]]; then
  echo "==> Packaging arXiv submission zip (temporary arxiv.tex at repo root for zip only)"
  cp -f "${BUILD}/arxiv.tex" "${ROOT}/arxiv.tex"
  bash scripts/package_arxiv_submit.sh --skip-tex-build
fi

cleanup
echo "==> Done (scratch tex removed)"
