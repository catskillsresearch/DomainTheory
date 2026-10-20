# DomainTheory

New repository scaffolded 2026-10-20 from the boilerplate of
[`scott_models`](https://github.com/catskillsresearch/scott_models)
(local source: `~/Desktop/archive/scott_models`, formerly `../scott_models`),
with the sibling Scott repos vendored under `vendor/` (see
`vendor/FROZEN.txt`).

## Copied boilerplate (from `scott_models`; scripts repointed to DomainTheory)

| Path | What |
| --- | --- |
| `.gitignore` | Lean/Lake, LaTeX, and generated-arXiv ignores |
| `.github/workflows/build.yml` | GitHub CI: install elan, `lake exe cache get`, `lake build` |
| `.latexmkrc`, `.cursorignore` | pdfLaTeX preview config; generated-artifact cursor ignores |
| `LICENSE` | Apache-2.0 |
| `scripts/build_arxiv_tex.{py,sh}`, `scripts/build_arxiv_pdf.sh` | Markdown (`arxiv.md`) → LaTeX (`arxiv.tex`) → PDF pipeline |
| `scripts/generate_arxiv_with_code.{py,sh}`, `scripts/package_arxiv_submit.sh`, `scripts/pdf_checks.sh` | Review-copy generation, arXiv zip packaging, font-embedding checks |
| `scripts/tex_preamble_arxiv.tex`, `scripts/lean_listing_sanitize.py`, `scripts/ai_model_cards.py`, `scripts/puppeteer-config.json` | Pipeline dependencies of `build_arxiv_tex.py` |
| `scripts/palomar_preflight.sh`, `scripts/compare_challenge_solution_types.sh` | Palomar setup: comparator/axiom/`sorry` preflight and Challenge-vs-Solution type diff |

## Vendored copies (`vendor/`)

Straight file copies (no `.git`, no `.lake`) of
[catskillsresearch](https://github.com/catskillsresearch) `scott1972`,
`scott1976`, `scott1980`, `scott1982`, and `scott_models` at the HEADs
recorded in `vendor/FROZEN.txt` — the same model as
`archive/scott_models/vendor/`. Note `vendor/scott_models/vendor/` is
upstream's own nested vendoring, kept as-is.

## Palomar provenance (initial, before modification)

`DomainTheory` is a derivative work building on those five vendored
repos, each Palomar-registered on its own as specified in its repo.
[`PROVENANCE.md`](PROVENANCE.md) tabulates each upstream, its frozen
vendored revision, its Palomar registration (ID + version + registry
link) and compared claim; [`formalization.yaml`](formalization.yaml)
(v0.4) is the **union of the five vendored `formalization.yaml` files,
in date order (1972, 1976, 1980, 1982, bridges)** — what would be
Palomared for `DomainTheory` is that union, under the renamed
`DomainTheory` declarations/files: 75 `main_results`, 90 alignment
statements grouped by base, merged sources (10, deduplicated),
classification, automation, gaps, and limitations, plus
`related_formalizations` with `/tree/<rev>` URLs matching
`vendor/FROZEN.txt`. The vendored code will change and diverge — the frozen
revisions are provenance before modification, not upstream identity,
and the upstream registrations are not transferred: `DomainTheory`
itself is not yet Palomar-registered and has no compared claim yet.

## Build

Pinned to Lean **v4.35.0** (`lean-toolchain`; toolchain itself lives in
`~/.elan/toolchains`, not in the repo) with Mathlib `v4.35.0`
(`lakefile.toml` / `lake-manifest.json`, mirroring the vendored repos'
setup files).

```bash
lake exe cache get
lake build   # DomainTheory.lean + all 316 submodule files
```

The single `DomainTheory` library assembles the five vendored
developments under renamed modules/namespaces — `DomainTheory.ContinuousLattice`
(ex-`Scott1972.ContinuousLattice`), `DomainTheory.DataTypesAsLattices`
(ex-`Scott1976.DataTypesAsLattices`), `DomainTheory.Neighborhood`
(ex-`Scott1980.Neighborhood`), `DomainTheory.InformationSystems`
(ex-`Scott1982`), `DomainTheory.BridgeTheorems` (ex-`ScottModels`) —
imported by the root `DomainTheory.lean`. Clean build verified
2026-10-20 (3505 jobs, no `sorry`). Ported v4.35 compatibility patches
are listed in `PROVENANCE.md` (“Assembly”).

## Not copied — needs authoring / adaptation

- No `Challenge.lean`/`Solution.lean` or `comparator.json` was copied.
  Those are `scott_models`-specific content, not boilerplate.
  `palomar_preflight.sh` will fail until a DomainTheory comparator and
  Challenge/Solution pair exist.
- Top-level `scripts/` now point at this repo
  (`github.com/catskillsresearch/DomainTheory`, Lean root `DomainTheory`):
  `build_arxiv_tex.py` uses that GitHub URL and the `DomainTheory/…`
  appendix-heading regex, and carries **no** Palomar URL — DomainTheory
  is not Palomar-registered yet, so the title page omits that line until
  `PALOMAR_URL` is set. `palomar_preflight.sh` parses all five vendor
  revisions from `vendor/FROZEN.txt` and scans `DomainTheory` +
  `Solution.lean` for `sorry`. `compare_challenge_solution_types.sh`
  reads its names from this repo's `comparator.json` (add structure
  constructors to its `EXTRA_PRINTS` as the library grows).
  `ai_model_cards.py` acknowledgements name DomainTheory and the five
  vendored siblings. References to Scott papers/siblings that remain
  are deliberate (vendored dependencies), not stale repo pointers.
- Nested `.gitignore` files under `vendor/` were removed; only the
  root `.gitignore` remains. It still matches some vendored generated
  artifacts, so commit those verbatim with `git add -f vendor/`.
