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
