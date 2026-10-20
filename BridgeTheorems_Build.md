# Build

```bash
lake exe cache get
lake build ScottModels
```

Pinned: Lean / mathlib v4.33.0. Sibling libraries are compiled from in-tree
`vendor/` (`srcDir`; frozen revisions and local patches in `vendor/FROZEN.txt`):
`scott1972` `278ba1745b6fb023fc3e9ffe53b7106ce60222c1`,
`scott1980` `ef6c05671582b7883ecd40b7081b642ce5351963`,
`scott1982` `d3221eec09505aa75e1b818aabc73f1f04339bdc`.
Palomar compared family: `Challenge.lean`, `Solution.lean`, `comparator.json`.
The narrative paper of record is this document (`view.pdf`).

Rebuild this document (PDF with complete Lean source appendix, one subsection per
module):

```bash
bash scripts/build_arxiv_pdf.sh            # expand Lean → tex → arxiv.pdf
bash scripts/build_arxiv_pdf.sh --pdf-only # PDF only when arxiv.tex already current
```
