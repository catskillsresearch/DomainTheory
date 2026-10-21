/-ai
Every cone is a neighbourhood of the binary-sequence system.

It is the first disjunct of the neighbourhood predicate, witnessed by its string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

theorem memC_cone (σ : Str) : memC (cone σ) := Or.inl ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Example44
