module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The neighbourhood-set of the union subdomain is exactly `⋃₀ ℱ`. -/
theorem unionSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    {X | (unionSys E ℱ hne hℱ hdir).mem X} = ⋃₀ ℱ := by
  ext X
  exact Set.mem_sUnion.symm

end DomainTheory.NeighbourhoodSystems.Proposition611
