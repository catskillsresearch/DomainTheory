/-ai
Two formulas are semantically equivalent if and only if they have the same Cantor-space evaluation.

If they agree under every valuation, extending a point and rewriting membership by the bridge between Cantor-space evaluation and truth shows that the two evaluations contain the same points. Conversely, equality of the evaluations makes an arbitrary valuation lie in one evaluation if and only if it lies in the other. The bridge turns that into a comparison of truth values, and the four combinations of Boolean values give equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_evalSet'_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- No finitary agreement argument is needed here (contrast `8.13(b)`'s `semanticEquiv_iff_
evalSet_eq`): `evalV`'s own domain `ℕ → Bool` already *is* Cantor space's points. -/
theorem semanticEquiv_iff_evalSet'_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet' φ = evalSet' ψ := by
  constructor
  · intro h
    ext x
    rw [mem_evalSet'_iff, mem_evalSet'_iff, h]
  · intro h v
    have hmem : v ∈ evalSet' φ ↔ v ∈ evalSet' ψ := by rw [h]
    rw [mem_evalSet'_iff, mem_evalSet'_iff] at hmem
    rcases hφ : evalV v φ with - | - <;> rcases hψ : evalV v ψ with - | - <;> simp_all

end DomainTheory.NeighbourhoodSystems
