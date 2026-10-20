# Provenance

`DomainTheory` is a **derivative work**. It starts from straight file
copies of five same-author (Lars Warren Ericson) Lean 4 formalizations,
vendored under `vendor/` on 2026-10-20, and builds on them. This file —
together with `vendor/FROZEN.txt` and `formalization.yaml` — records
that starting point **before modification**: the vendored code is
expected to change and diverge from the upstream repositories as
`DomainTheory` develops, and the frozen revisions below are the
provenance of the copies, not a claim that the trees will stay
identical to upstream.

Dana Scott did not participate in, review, or endorse any of the
vendored formalizations (per their own `PROVENANCE.md` files), and does
not endorse this derivative work either. The Scott papers are cited as
literature only.

## Bases (vendored, 2026-10-20)

Each base is registered with [Palomar](https://palomar-registry.org/about)
on its own, as specified in that repository (badge in its `README.md`,
statement in its `PROVENANCE.md`, metadata in its `formalization.yaml`)
at the vendored revision. The Palomar ID and version below are quoted
from the vendored repos; the vendored revision is the upstream git HEAD
copied here, and is **not** asserted to be the separate pinned commit
Palomar preserves for that entry.

| Vendored copy | Upstream | Vendored rev | Palomar registration (as specified in the repo) | Upstream compared claim |
| --- | --- | --- | --- | --- |
| `vendor/scott1972` | [`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972) | `a198b6e24aea07cfc858a59798d0ca78161c4387` | [PALOMAR-2026-08-24-000003](https://palomar-registry.org/entry?id=PALOMAR-2026-08-24-000003&version=2) (version 2) | Theorem 4.4 of *Continuous Lattices* (LNM 274, 1972): the inverse limit `D∞` is a continuous lattice homeomorphic to `[D∞ → D∞]` (`Scott1972.ContinuousLattice.theorem_4_4`; comparator: 19 theorems, 15 definitions) |
| `vendor/scott1976` | [`catskillsresearch/scott1976`](https://github.com/catskillsresearch/scott1976) | `94ef7f7f096078cbfe4f99595c2a3fcb4c563942` | [PALOMAR-2026-08-25-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000004&version=1) (version 1) | Selected declarations of *Data Types as Lattices* (PRG-5, 1976; SIAM J. Comput. 5 (1976), 522–587) — comparator: 63 theorems, 70 definitions in `Scott1976.DataTypesAsLattices` |
| `vendor/scott1980` | [`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980) | `11b25d2e9cc32176ddfc78194058c61a0138a6da` | [PALOMAR-2026-08-24-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-08-24-000001&version=2) (version 2) | First sentence of Theorem 8.8 of *Lectures on a Mathematical Theory of Computation* (PRG-19, 1980/May 1981): every countable neighbourhood system embeds in the universal domain (`D ⊴ U`), plus the `P4_embeds` and `Ssys_embeds` corollaries (comparator: 19 theorems, 13 definitions) |
| `vendor/scott1982` | [`catskillsresearch/scott1982`](https://github.com/catskillsresearch/scott1982) | `455bd70226912fa621203319292e25deb0677082` | [PALOMAR-2026-08-24-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-08-24-000005&version=1) (version 1) | First sentence of Theorem 7.2 of *Domains for Denotational Semantics* (ICALP 1982): approximable mappings `A → B` are exactly the elements of `\|A → B\|` (`Scott1982.InfoSys.theorem_7_2`; comparator: 28 theorems, 13 definitions) |
| `vendor/scott_models` | [`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models) | `85ed1ae09faa29fe292c9867e91cf8e9b48ab2fa` | [PALOMAR-2026-08-25-000003](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000003&version=1) (version 1) | Cross-presentation bridges between the 1972 continuous-lattice, 1980 neighbourhood-system, and 1982 information-system presentations, including `D ≃o RoundFilter ≃o RoundInfoSysElement` and the S-expression equation `\|T\| ≃o \|A + (T × T)\|` (comparator: 4 theorems, 28 definitions). This tree in turn vendors its own copies of `scott1972`/`scott1980`/`scott1982` under `vendor/scott_models/vendor/`, kept as-is |

Full upstream URLs at the vendored revisions
(`https://github.com/catskillsresearch/<repo>/tree/<rev>`) are listed
machine-readably in `formalization.yaml` under
`related_formalizations`, so `scripts/palomar_preflight.sh` can match
them against `vendor/FROZEN.txt`.

## Status of this repository

- `DomainTheory` itself is **not yet Palomar-registered**, has no
  Palomar statement of record, and has no `Challenge.lean`,
  `Solution.lean`, or `comparator.json` yet. Nothing here transfers,
  inherits, or re-claims the five registrations above; they remain the
  registrations of the upstream repositories, whose remotes remain the
  per-paper homes.
- This is an initial-provenance record, set up before any `DomainTheory`
  Lean development. When a compared claim is chosen, it will need its
  own `comparator.json`, Challenge/Solution pair, and — if submitted —
  its own Palomar registration, with this file and
  `formalization.yaml` updated to describe the derivative development
  rather than only its bases.
- The five vendored formalizations are the **derived-from sources**:
  `DomainTheory` may adapt their Lean code, proof patterns, and
  narrative. Post-2026-10-20 changes inside `vendor/` (or code moved
  out of it) are `DomainTheory` modifications, attributable to this
  repository's git history — not to the upstream repos or their
  Palomar entries. Consult each vendored repo's own `formalization.yaml`
  for the automation/review history of the code as copied; that history
  is not restated as `DomainTheory`'s own.

## Deviations already present at setup

The copies are straight file copies of the upstream tracked trees with
every `.git` directory removed (no `.lake` was present in the clones).
Two deviations exist before any Lean modification:

1. Nested `.gitignore` files under `vendor/` (including inside
   `vendor/scott_models/vendor/`) were removed on 2026-10-20; only this
   repository's root `.gitignore` remains.
2. Top-level boilerplate (`LICENSE`, `.github/workflows/build.yml`,
   `scripts/` for the `arxiv.md` → LaTeX pipeline and Palomar
   preflight, `.gitignore`, `.latexmkrc`, `.cursorignore`) was copied
   from `scott_models` and repointed to this repository — those
   top-level files are scaffolding, not part of any vendored
   formalization.

## Relation to the earlier `domain_theory`

[`catskillsresearch/domain_theory`](https://github.com/catskillsresearch/domain_theory)
was an earlier combined tree, archived as the per-paper split
progressed (see `vendor/scott_models/PROVENANCE.md`); `scott_models`
records itself as superseding it. It is a historical predecessor, is
not vendored here, and is not one of the five bases above. This
repository (`DomainTheory`) is a new derivative development from the
five registered per-paper/bridge repos, not a continuation claim on
the archived tree's history.

## Licence and authorship

All five bases and this repository are Apache-2.0 (see `LICENSE`), by
the same author, so this is a derivative of the author's own split
development, not a republication of someone else's formalization. The
human author retains sole responsibility for the mathematical content
and for every change made after the frozen copies.

## Assembly (2026-10-20, post-provenance modification)

After the pre-modification record above, the vendored libraries were
copied into `DomainTheory/` and assembled as one Lean library pinned
to Lean/Mathlib v4.35.0 (`lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`; `lake build` green, no `sorry`):

- `DomainTheory/ContinuousLattice{,.lean}` ← `vendor/scott1972/Scott1972{,.lean}`
- `DomainTheory/DataTypesAsLattices{,.lean}` ← `vendor/scott1976/Scott1976{,.lean}`
- `DomainTheory/Neighborhood{,.lean}` ← `vendor/scott1980/Scott1980{,.lean}`
- `DomainTheory/InformationSystems{,.lean}` ← `vendor/scott1982/Scott1982{,.lean}`
- `DomainTheory/BridgeTheorems{,.lean}` ← `vendor/scott_models/ScottModels{,.lean}`

All module paths, namespaces, and qualified references were renamed
(`Scott1972.ContinuousLattice` → `DomainTheory.ContinuousLattice`,
`Scott1976.DataTypesAsLattices` → `DomainTheory.DataTypesAsLattices`,
`Scott1980.Neighborhood` → `DomainTheory.Neighborhood`,
`Scott1982` → `DomainTheory.InformationSystems`,
`ScottModels` → `DomainTheory.BridgeTheorems`); root `DomainTheory.lean`
imports the five aggregators. Compatibility patches needed for
Lean/Mathlib v4.35.0 (the bases were pinned at v4.33.0/v4.30.0):

- `InformationSystems`: ported the patches already present in
  `vendor/scott_models/vendor/scott1982` — `Constructive.funion_empty_right`,
  the `Proposition23`/`Fixpoint`/`Theorem72` `change`-based proofs, the
  extensional `Factoid82.lamDForget_listToLamDFinset` proof, wholesale
  `Factoid77` (explicit tensor/product transports) and `Factoid81`
  (bridge `TreeEntPayload` disjuncts, `TreeCon_insert_bot`, handwritten
  `instDecidableEqTreeToken`, `Type u` tokens), and named instances in
  `InfoSys`/`Product`/`Sum`.
- `Neighborhood`: new v4.35 fixes — `wellFounded_lt.has_min`
  (`Exercise125`), `by_cases` replacing `rcases … Nat.decEq … with h | h`
  (which no longer introduces names in v4.35) in `Exercise221`,
  `Recursive`, `Theorem74`, `Theorem88i`, `Theorem88l`,
  `DAtomDecidable`, and the new `εNFA.εClosure_induction` /
  `subset_εClosure` / `mem_εClosure_of_mem_step` API (`Exercise722Cat`).

`vendor/` itself was not modified by the assembly; divergence is in
`DomainTheory/` only.

## Union formalization (2026-10-20)

`formalization.yaml` is now the union, in date order 1972 → 1976 →
1980 → 1982 → bridges, of the five vendored `formalization.yaml`
files: what would be Palomared for `DomainTheory` is that union,
expressed under the renamed `DomainTheory` declarations and file
paths (75 `main_results` and 90 alignment statements, all verified to
exist by `#check` against the built library; 10 deduplicated
sources; merged classification/automation/known-gaps/limitations).
The union does not itself register `DomainTheory`: a merged
`comparator.json` (union of the five `vendor/*/comparator.json` name
lists, renamed) and a Challenge/Solution pair remain to be authored.
