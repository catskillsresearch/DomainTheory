module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.RunMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.eq_runMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems.RunMap

/-- Scott's Example 2.4: erasing the first run of ones defines an approximable
endomap of the binary-tree system satisfying the run equations. -/
theorem example_2_4 :
    (∀ τ, out ([false] ++ τ) = false :: out τ) ∧
    (∀ τ, out ([true, false] ++ τ) = false :: τ) ∧
    (∀ τ, out ([true, true] ++ τ) = out ([true] ++ τ)) ∧
    SatisfiesRunEquations runMap :=
  ⟨out_append_false, out_append_trueFalse, out_append_trueTrue, runMap_satisfies⟩
