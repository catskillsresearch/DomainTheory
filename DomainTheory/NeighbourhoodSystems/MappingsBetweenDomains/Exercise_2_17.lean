module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.eq_runMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open RunMap

/-- Scott's Exercise 2.17: the erase-ones map is uniquely determined by the run equations, and
those equations hold of the erase-ones map. -/
theorem exercise_2_17 :
    (∀ {g : ApproximableMap BitDom.B BitDom.B},
      SatisfiesRunEquations g → g = runMap) ∧
    SatisfiesRunEquations runMap :=
  ⟨@eq_runMap_of_satisfies, runMap_satisfies⟩
