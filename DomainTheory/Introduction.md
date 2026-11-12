# Introduction

@import "../DomainTheory.mermaid"

This combined library is registered with
[Palomar](https://palomar-registry.org/about) as
**[PALOMAR-2026-11-12-000010](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-12-000010&version=1)**,
version 1 [@palomar-2026-11-12-000010-v1].

DomainTheory is a single Lean 4 / Mathlib library (v4.36.0-rc2, `lake build`
green, no `sorry`) assembled from five prior Palomar-registered
formalizations, each with a public GitHub home under
`catskillsresearch`, and vendored in the DomainTheory GitHub repository
[@github-DomainTheory] under `vendor/` for provenance:

- *Continuous Lattices* (1972) — Palomar
  [@palomar-2026-08-24-000003-v2], GitHub [@github-scott1972], and arXiv
  preprint [@Ericson26ContinuousLattices];
- *Data Types as Lattices* (1976) — Palomar
  [@palomar-2026-08-25-000004-v1] and GitHub [@github-scott1976];
- neighbourhood systems / PRG-19 (1980) — Palomar
  [@palomar-2026-08-24-000001-v2] and GitHub [@github-scott1980];
- information systems (1982) — Palomar
  [@palomar-2026-08-24-000005-v1] and GitHub [@github-scott1982];
- cross-presentation bridges (`scott_models`) — Palomar
  [@palomar-2026-08-25-000003-v1] and GitHub [@github-scott_models].

The working Lean is the golfed `DomainTheory/` tree:
`ContinuousLattice` ← 1972, `DataTypesAsLattices` ← 1976,
`NeighbourhoodSystems` ← 1980, `InformationSystems` ← 1982,
`BridgeTheorems` ← `scott_models`. Comparator (`Challenge.lean` /
`Solution.lean` / `comparator.json`) validates (i) the cross-presentation
bridges of [@palomar-2026-08-25-000003-v1] (1972 continuous-lattice /
1980 neighbourhood / 1982 information-system isomorphisms, including
$D \simeq_o$ RoundFilter $\simeq_o$ RoundInfoSysElement and the S-expression
equation $|T| \simeq_o |A + (T \times T)|$), and (ii) the selected *Data
Types as Lattices* (1976) declarations of [@palomar-2026-08-25-000004-v1].
That 1976 selection is not only the retract and algebraic-lattice
development on $\mathbf{P}\omega$: it also covers Scott's computability
apparatus for the universal domain (the language LAMBDA, enumeration and
recursion, definability, and enumeration degrees as combinatory
subalgebras) and the descriptive-set style classification of subsets of
$\mathbf{P}\omega$ (open, closed, $\mathfrak{G}_\delta$, Boolean, and related
classes characterized as fibres of continuous maps). The golfed library
preserves those validated results under Mathlib-style names. The Lean
sources and frozen vendor trees live in [@github-DomainTheory]; this
document is the accompanying CMU-CS technical report.

**Author contributions.** Lars Warren Ericson — primary formalization
engineer (all Lean 4, AI-assisted proof architecture, repository assembly);
Dana S. Scott — author of the original source mathematics (1972–1982),
project sponsorship, historical context, and high-level advisory oversight
of formalization scope; Vijay D'Silva and Brian Milnes — project initiation,
pre-submission review, and advisory feedback on repository formatting and
technical report generation. Source-paper authorship is distinct from
combined-library co-authorship; Scott, D'Silva, and Milnes did not write the
Lean.
