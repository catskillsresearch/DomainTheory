#!/usr/bin/env bash
# Flatten DomainTheory.md (if arxiv.md is missing/stale), copy to arxiv_with_code.md,
# then build arxiv.tex + listings/figures.
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT_MD="DomainTheory.md"
if [[ ! -f arxiv.md ]] || [[ "$ROOT_MD" -nt arxiv.md ]]; then
  echo "==> Flattening $ROOT_MD → arxiv.md"
  python3 scripts/compile_md_tree.py --md-only
fi

echo "==> Regenerating arxiv_with_code.md (from arxiv.md)"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py
