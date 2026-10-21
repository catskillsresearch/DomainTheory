/-ai
The set of neighbourhoods of the intersection subdomain is the intersection of the family.

A set is a neighbourhood of the intersection system exactly when it belongs to every member of the family, which is membership in that intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The neighbourhood-set of the intersection subdomain is exactly `⋂₀ ℱ`. -/
theorem interSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) :
    {X | (interSys E ℱ hne hℱ).mem X} = ⋂₀ ℱ := by
  ext X
  exact Set.mem_sInter.symm

end DomainTheory.NeighbourhoodSystems.Proposition611
