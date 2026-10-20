module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.memO

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nestedOrDisjoint_O : NestedOrDisjoint memO := by
  rintro X Y (rfl | rfl) (rfl | rfl)
  · exact Or.inl subset_rfl
  · exact Or.inr (Or.inl (Set.empty_subset _))
  · exact Or.inl (Set.empty_subset _)
  · exact Or.inl subset_rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
