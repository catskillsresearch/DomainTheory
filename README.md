# DomainTheory

Lean 4 / Mathlib formalization of Dana Scott’s domain-theory papers
(continuous lattices 1972, data types as lattices 1976, neighbourhood
systems 1980, information systems 1982), plus cross-presentation bridges.
The working library is under `DomainTheory/`; five earlier per-paper
repositories are frozen under `vendor/` for provenance.

**Authors:** Lars Warren Ericson, Dana Scott, Vijay d'Silva, Brian Milnes
(Apache-2.0). Ericson wrote the Lean; Scott is the source mathematician and
advises on scope; D'Silva and Milnes helped initiate the project and review
packaging. Full contribution statement: [`PROVENANCE.md`](PROVENANCE.md).

## Library

| Module | Source |
| --- | --- |
| `DomainTheory.ContinuousLattice` | Scott 1972 |
| `DomainTheory.DataTypesAsLattices` | Scott 1976 |
| `DomainTheory.NeighbourhoodSystems` | Scott 1980 |
| `DomainTheory.InformationSystems` | Scott 1982 |
| `DomainTheory.BridgeTheorems` | bridges among the three presentations |

Root `DomainTheory.lean` imports every leaf. Palomar Comparator covers the
bridges and a selected 1976 slice (`Challenge.lean`, `Solution.lean`,
`comparator.json`, [`formalization.yaml`](formalization.yaml)). Upstream
registrations and frozen revisions are tabulated in
[`PROVENANCE.md`](PROVENANCE.md); they are not transferred to this repo.

## Revision

The vendored formalizations kept each paper statement with its proof under
a paper-derived name. This revision gives mathematical facts Mathlib-style
names, keeps Scott’s prose in order, and proves each paper proposition by
calling those lemmas. Proposition 2.2 is the pattern: `bot_wayBelow`,
`WayBelow.sup`, `WayBelow.trans_le`, `WayBelow.le_trans`, `WayBelow.le`,
`WayBelow.self_iff_scottOpen_Ici`, and `WayBelow.sSup_iff` are the tools;
`proposition_2_2` is Scott’s statement.

1972 section progress:
[`DomainTheory/ContinuousLattice/1972_REVISION.md`](DomainTheory/ContinuousLattice/1972_REVISION.md).

## Build

Toolchain: Lean / Mathlib **v4.36.0-rc2** (`lean-toolchain`, `lakefile.toml`).

```bash
lake exe cache get
python3 scripts/check_domaintheory_barrel.py    # DomainTheory/**/*.lean in DomainTheory.lean
python3 scripts/check_md_hierarchy_lean.py      # Lean linked from DomainTheory.md
python3 scripts/sync_missing_lean_hierarchy.py  # attach unlinked Lean via import graph
lake build
```

Before a Palomar submission, run `scripts/palomar_preflight.sh` (or the
external editorial wrapper). Assembly notes and v4.35→v4.36 porting detail
live in [`PROVENANCE.md`](PROVENANCE.md).
