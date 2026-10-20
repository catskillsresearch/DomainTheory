module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `𝒪` is closed under intersection (used to verify the relation of `openToMap`). -/
theorem O_inter_mem {Y Y' : Set (Fin 1)} (hY : O.mem Y) (hY' : O.mem Y') : O.mem (Y ∩ Y') := by
  rcases hY with rfl | rfl
  · rw [Set.univ_inter]; exact hY'
  · rw [Set.empty_inter]; exact O_mem_empty

end DomainTheory.NeighbourhoodSystems.Exercise215
