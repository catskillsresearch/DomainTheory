/-ai
The intersection subdomain is a subsystem of E.

The masters agree. A neighbourhood of the intersection belongs to some member of the family, hence is a neighbourhood of E. If two such neighbourhoods have an intersection that is a neighbourhood of E, that intersection belongs to every member of the family by the intersection-closure of subdomain neighbourhood-sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.interSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The intersection subdomain is a subsystem of `E`. -/
theorem interSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : interSys E ℱ hne hℱ ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
  inter_closed := by
    intro X Y hX hY hEXY 𝒮 h𝒮
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) hEXY

end DomainTheory.NeighbourhoodSystems.Proposition611
