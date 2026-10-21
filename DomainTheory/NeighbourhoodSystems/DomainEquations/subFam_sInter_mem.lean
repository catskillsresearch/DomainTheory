/-ai
The family of subdomain neighbourhood-sets is closed under nonempty intersections.

The intersection system of such a family is a subsystem of E, and the collection of its neighbourhoods is the intersection of the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys_nbset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- **Closure under non-empty intersection** (Exercise 2.22's hypothesis (i)). -/
theorem subFam_sInter_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : ⋂₀ ℱ ∈ subFam E :=
  ⟨interSys E ℱ hne hℱ, interSys_subsystem E ℱ hne hℱ, (interSys_nbset E ℱ hne hℱ).symm⟩

end DomainTheory.NeighbourhoodSystems.Proposition611
