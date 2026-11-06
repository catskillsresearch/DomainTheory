module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.powerSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

/-- Scott's Exercise 2.20: under the identification of ideal elements with subsets of ℕ,
union and intersection are binary approximable maps, and successor/predecessor of sets are
approximable. -/
theorem example_220 :
    (∀ (x y : powerSet.Element),
      toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y) ∧
    (∀ (x y : powerSet.Element),
      toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y) ∧
    (∀ (x : powerSet.Element), toSet (succMap.toElementMap x) = succSet (toSet x)) ∧
    (∀ (x : powerSet.Element), toSet (predMap.toElementMap x) = predSet (toSet x)) :=
  ⟨toSet_unionMap, toSet_interMap₂, toSet_succMap, toSet_predMap⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
