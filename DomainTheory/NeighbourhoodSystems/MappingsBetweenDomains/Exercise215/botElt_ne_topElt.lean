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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `⊥ ≠ ⊤` (so `⊥ ⊏ ⊤`). -/
theorem botElt_ne_topElt : botElt ≠ topElt := by
  intro h
  have htop : topElt.mem ∅ := ⟨O_mem_empty, subset_rfl⟩
  rw [← h, mem_botElt] at htop
  exact univ_ne_empty htop.symm

end DomainTheory.NeighbourhoodSystems.Exercise215
