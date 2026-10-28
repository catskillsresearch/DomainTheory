#!/usr/bin/env bash
# Flatten root markdown → arxiv.md (or $ARXIV_MD), then arxiv.tex + listings/figures.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"

ROOT_MD="${ARXIV_ROOT_MD:-${ROOT}/DomainTheory.md}"
MD_OUT="${ARXIV_MD:-${ROOT}/arxiv.md}"

# Always refresh note @imports and re-flatten. Nested notes change without
# touching the root note; skipping left stale PDFs pointing at deleted Prefs.
echo "==> Refreshing notes + flattening $(basename "$ROOT_MD") → $(basename "$MD_OUT")"
python3 scripts/compile_md_tree.py --md-only --root "$ROOT_MD" --out "$MD_OUT"

echo "==> Regenerating $(basename "${ARXIV_WITH_CODE:-arxiv_with_code.md}") (from $(basename "$MD_OUT"))"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building $(basename "${ARXIV_TEX:-arxiv.tex}") + lean-listings/ + figures/"
python3 scripts/test_lean_listing_sanitize.py
python3 scripts/test_set_comprehension_repair.py
python3 scripts/build_arxiv_tex.py
