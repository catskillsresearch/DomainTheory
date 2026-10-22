module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.toElementMap_openToMap_principal_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.isOpen_mapToOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (map → open → map).** `openToMap (mapToOpen f) = f`. -/
theorem openToMap_mapToOpen (f : ApproximableMap V O) :
    openToMap V (mapToOpen V f) (isOpen_mapToOpen V f) = f := by
  apply ApproximableMap.eq_of_toElementMap_principal
  intro X hX
  apply O_ext
  rw [toElementMap_openToMap_principal_mem_empty, mapToOpen, Set.mem_ofPred_eq,
    ← mem_empty_iff_eq_top]

end DomainTheory.NeighbourhoodSystems.Exercise215
