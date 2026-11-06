module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.hMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

/-- Scott's Exercise 2.18: the insert-zero map is not surjective, has a left inverse, and that
left inverse is not injective. -/
theorem example_218 :
    (¬ Function.Surjective hMap.toElementMap) ∧
    (kMap.comp hMap = ApproximableMap.idMap ExampleB.B) ∧
    (¬ Function.Injective kMap.toElementMap) :=
  ⟨hMap_not_surjective, kMap_comp_hMap, kMap_not_injective⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
