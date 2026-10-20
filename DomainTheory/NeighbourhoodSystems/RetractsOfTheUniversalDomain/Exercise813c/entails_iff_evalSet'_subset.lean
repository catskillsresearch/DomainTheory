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

/-- The same finitary-free argument as `semanticEquiv_iff_evalSet'_eq`, for entailment. -/
theorem entails_iff_evalSet'_subset {φ ψ : Formula} :
    Entails φ ψ ↔ evalSet' φ ⊆ evalSet' ψ := by
  constructor
  · intro h x hx
    rw [mem_evalSet'_iff] at hx ⊢
    exact h _ hx
  · intro h v hv
    exact (mem_evalSet'_iff v ψ).mp (h ((mem_evalSet'_iff v φ).mpr hv))

end DomainTheory.NeighbourhoodSystems
