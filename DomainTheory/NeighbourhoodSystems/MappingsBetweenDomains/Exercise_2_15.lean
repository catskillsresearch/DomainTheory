module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.O

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.O

/-- Scott's Exercise 2.15: opens of a domain are classified by approximable maps into the
one-token Sierpiński system. -/
theorem example_215 :
    (∀ {γ : Type*} (V : NeighborhoodSystem γ) (U : Set V.Element) (hU : IsOpen U)
      (x : V.Element), x ∈ mapToOpen V (openToMap V U hU) ↔ x ∈ U) ∧
    (∀ {γ : Type*} (V : NeighborhoodSystem γ) (f : ApproximableMap V system),
      openToMap V (mapToOpen V f) (isOpen_mapToOpen V f) = f) :=
  ⟨@mem_mapToOpen_openToMap, @openToMap_mapToOpen⟩
