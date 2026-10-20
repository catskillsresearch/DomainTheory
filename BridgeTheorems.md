# Equivalence of Scott's Three Presentations of Domain Theory

Dana Scott developed three presentations of the same class of domains: **continuous
lattices** (1972), **neighbourhood systems** (PRG-19 / 1980–81), and **information
systems** (1982). In this chapter we supply **bridge theorems**: order
isomorphisms and constructivity audits showing that the three presentations determine
the same domains (up to isomorphism), including products, separated sums, and function
spaces at the information-system level, with a transport of 1972 Scott maps along the
round presentation.

The Lean development is sorry-free. The continuous-lattice identification
`D ≃o RoundFilter` audits to `{propext, Quot.sound}`. Every InfoSys-facing
declaration inherits `Classical.choice` from Mathlib 4.33’s `Finset` instances,
even when the proof term extracts no witness. Genuine classical frontiers remain
Scott’s 1972 topological definition of `≪` (algebraic ⇒ continuous; ScottMap
conjugation) and trichotomy for separated sums.

- [Introduction](BridgeTheorems_Introduction.md)
- [Catalog of bridge theorems](BridgeTheorems_Catalog_of_bridge_theorems.md)
- [Proof notes](BridgeTheorems_Proof_notes.md)
- [Constructivity summary](BridgeTheorems_Constructivity_summary.md)
- [Worked example — S-expressions / trees](BridgeTheorems_Worked_example.md)

**Lean 4**

- [BridgeTheorems.lean](DomainTheory/BridgeTheorems.lean)
