/-ai
The basic open of the empty neighbourhood is the singleton of the top element.

Extensionality reduces the equality to membership. An element lies in that basic open exactly when it contains the empty set, and it contains the empty set exactly when it is the top element, which is membership in the singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- The open point `{⊤}` is the basic open `[∅]`. -/
theorem basicOpen_empty_eq_singleton_top : O.basicOpen ∅ = {topElt} := by
  ext x
  rw [mem_basicOpen, mem_empty_iff_eq_top]
  exact Set.mem_singleton_iff.symm

end DomainTheory.NeighbourhoodSystems.Exercise215
