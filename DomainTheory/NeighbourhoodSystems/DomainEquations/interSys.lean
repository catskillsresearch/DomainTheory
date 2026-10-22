module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_master_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The **intersection subdomain** of a non-empty family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are the sets common to *every* member of `ℱ`. -/
def interSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : NeighborhoodSystem α where
  mem X := ∀ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := fun 𝒮 h𝒮 => subFam_master_mem E (hℱ h𝒮)
  inter_mem := by
    intro X Y Z hX hY hZ hsub 𝒮 h𝒮
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮) (hY 𝒮 h𝒮)
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮) (hZ 𝒮 h𝒮)
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) (E.inter_mem hEX hEY hEZ hsub)
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮))

end DomainTheory.NeighbourhoodSystems.Proposition611
