module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem fiber_encSet_none {σ : Str} {i : ℕ} (h : σ[i]? = none) :
    fiber (encSet σ) i = Set.univ := by
  ext t
  simp only [mem_fiber, mem_encSet, Set.mem_univ, iff_true]
  intro b hb; rw [h] at hb; exact absurd hb (by simp)

end DomainTheory.NeighbourhoodSystems.Exercise317
