module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.hMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.HMap
/-- Scott's Exercise 2.18: the insert-zero map is not surjective, has a left inverse, and that
left inverse is not injective. -/
theorem example_218 :
    (¬ Function.Surjective hMap.toElementMap) ∧
    (kMap.comp hMap = ApproximableMap.idMap BitDom.B) ∧
    (¬ Function.Injective kMap.toElementMap) :=
  ⟨hMap_not_surjective, kMap_comp_hMap, kMap_not_injective⟩
