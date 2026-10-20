module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.toElementMap_openToMap_principal_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (open → map → open).** `mapToOpen (openToMap U hU) = U`. -/
theorem mem_mapToOpen_openToMap (U : Set V.Element) (hU : IsOpen U) (x : V.Element) :
    x ∈ mapToOpen V (openToMap V U hU) ↔ x ∈ U := by
  rw [mapToOpen, Set.mem_ofPred_eq, ← mem_empty_iff_eq_top,
    ApproximableMap.toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    rw [toElementMap_openToMap_principal_mem_empty] at hmem
    have hple : V.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact V.isOpen_isUpperSet hU hmem hple
  · intro hxU
    obtain ⟨X, hxX, hXU⟩ := hU x hxU
    refine ⟨X, hxX, ?_⟩
    rw [toElementMap_openToMap_principal_mem_empty]
    exact hXU (show V.principal (x.sub hxX) ∈ V.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise215
