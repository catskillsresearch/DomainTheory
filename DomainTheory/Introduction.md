# Introduction

@import "../DomainTheory.mermaid"

This combined library is registered with
[Palomar](https://palomar-registry.org/about) as
**[PALOMAR-2026-11-12-000010](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-12-000010&version=1)**,
version 1 [@palomar-2026-11-12-000010-v1].

DomainTheory is a single Lean 4 / Mathlib library (v4.36.0-rc2, `lake build`
green, no `sorry`) assembled from five Palomar-registered formalizations
vendored under `vendor/` for provenance (`scott1972`, `scott1976`,
`scott1980`, `scott1982`, `scott_models`; see `PROVENANCE.md` and
`vendor/FROZEN.txt`). The working Lean is the golfed `DomainTheory/` tree:
`ContinuousLattice` ← 1972, `DataTypesAsLattices` ← 1976,
`NeighbourhoodSystems` ← 1980, `InformationSystems` ← 1982,
`BridgeTheorems` ← `scott_models`. Comparator (`Challenge.lean` /
`Solution.lean` / `comparator.json`) validates (i) the cross-presentation
bridges formerly registered as `scott_models` (1972 continuous-lattice /
1980 neighbourhood / 1982 information-system isomorphisms, including
$D \simeq_o$ RoundFilter $\simeq_o$ RoundInfoSysElement and the S-expression
equation $|T| \simeq_o |A + (T \times T)|$), and (ii) the selected *Data
Types as Lattices* (1976) declarations formerly registered as `scott1976`.
That 1976 selection is not only the retract and algebraic-lattice
development on $\mathbf{P}\omega$: it also covers Scott's computability
apparatus for the universal domain (the language LAMBDA, enumeration and
recursion, definability, and enumeration degrees as combinatory
subalgebras) and the descriptive-set style classification of subsets of
$\mathbf{P}\omega$ (open, closed, $\mathfrak{G}_\delta$, Boolean, and related
classes characterized as fibres of continuous maps). The golfed library
preserves those validated results under Mathlib-style names. Distribution
today is the public GitHub repository only; a CMU-CS technical report
(CMU-CS-TR) is planned.

**Author contributions.** Lars Warren Ericson — primary formalization
engineer (all Lean 4, AI-assisted proof architecture, repository assembly);
Dana S. Scott — author of the original source mathematics (1972–1982),
project sponsorship, historical context, and high-level advisory oversight
of formalization scope; Vijay D'Silva and Brian Milnes — project initiation,
pre-submission review, and advisory feedback on repository formatting and
technical report generation. Source-paper authorship is distinct from
combined-library co-authorship; Scott, D'Silva, and Milnes did not write the
Lean.
