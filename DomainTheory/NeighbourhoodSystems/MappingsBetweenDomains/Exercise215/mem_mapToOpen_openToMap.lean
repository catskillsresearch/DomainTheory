/-ai
An element lies in the open set of the approximable map of an open set if and only if it lies in that open set.

Membership in the open set of the map means that the element map sends the element to the top element, hence that the image contains the empty set, which means that some neighbourhood of the element is related to the empty set. That relation holds exactly when the principal filter of the neighbourhood lies in the open set. Such a principal filter lies below the element, and an open set is an upper set, so the element lies in the open set. In the other direction, openness supplies a neighbourhood whose basic open is contained in the open set, and the principal filter of that neighbourhood lies in the basic open.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.toElementMap_openToMap_principal_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen

@[expose] public section

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
    obtain ⟨X, hxX, hXU⟩ := hU.out x hxU
    refine ⟨X, hxX, ?_⟩
    rw [toElementMap_openToMap_principal_mem_empty]
    exact hXU (show V.principal (x.sub hxX) ∈ V.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise215
