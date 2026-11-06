module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.eq_runMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24

/-- Scott's Exercise 2.17: the erase-ones map is uniquely determined by the run equations, and
those equations hold of the erase-ones map. -/
theorem exercise_2_17 :
    (∀ {g : ApproximableMap ExampleB.B ExampleB.B},
      SatisfiesRunEquations g → g = runMap) ∧
    SatisfiesRunEquations runMap :=
  ⟨@eq_runMap_of_satisfies, runMap_satisfies⟩

end DomainTheory.NeighbourhoodSystems.Example24
