module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The **union subdomain** of a directed family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are those lying in *some* member of `ℱ`. Directedness is what makes this closed
under consistent intersection. -/
def unionSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    NeighborhoodSystem α where
  mem X := ∃ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := by
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact ⟨𝒮, h𝒮, subFam_master_mem E (hℱ h𝒮)⟩
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮z, h𝒮z, hZz⟩ := hZ
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    have hXs : X ∈ 𝒮s := hxs hXx
    have hYs : Y ∈ 𝒮s := hys hYy
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮s) hXs
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮s) hYs
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮z) hZz
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) hXs hYs (E.inter_mem hEX hEY hEZ hsub)⟩
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) hX𝒮)

end DomainTheory.NeighbourhoodSystems.Proposition611
