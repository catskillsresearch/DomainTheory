module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.memO
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.topElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openSet_equiv_map
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.univ_ne_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.nestedOrDisjoint_O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.subMaster_O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_inter_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.element_eq_bot_or_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.toElementMap_openToMap_principal_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.isOpen_mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_mapToOpen_openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap_mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt_ne_topElt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **The opens of `|𝒪|`.** `{⊥}` is not open: `⊥` is the generic point. (The basic neighbourhood of
`⊥` is `[Δ] = |𝒪|`, which is not contained in `{⊥}` because it also contains `⊤`.) -/
theorem not_isOpen_singleton_botElt : ¬ IsOpen ({botElt} : Set O.Element) := by
  intro h
  obtain ⟨X, hX, hsub⟩ := h botElt rfl
  rw [mem_botElt] at hX
  subst hX
  have htop : topElt ∈ ({botElt} : Set O.Element) :=
    hsub (show topElt ∈ O.basicOpen Set.univ from (O_master ▸ topElt.master_mem))
  exact botElt_ne_topElt (Set.mem_singleton_iff.mp htop).symm

end DomainTheory.NeighbourhoodSystems.Exercise215
