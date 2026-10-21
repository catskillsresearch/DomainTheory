/-ai
The singleton {0} is distinct from the set {0, 1} in Fin 2.

If the two sets were equal, 1 would belong to {0}. It does not.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem fin2_zero_ne_zero_one : ({0} : Set (Fin 2)) ≠ ({0, 1} : Set (Fin 2)) := by
  intro h
  have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
  rw [← h] at h1
  simp at h1

end DomainTheory.NeighbourhoodSystems
