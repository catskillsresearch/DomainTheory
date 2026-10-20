module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The union subdomain is a subsystem of `E` (Scott's remark: the directed union of subdomains is
again a subdomain). -/
theorem unionSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    unionSys E ℱ hne hℱ hdir ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact subFam_mem_E E (hℱ h𝒮) hX𝒮
  inter_closed := by
    intro X Y hX hY hEXY
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) (hxs hXx) (hys hYy) hEXY⟩

end DomainTheory.NeighbourhoodSystems.Proposition611
