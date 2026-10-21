/-ai
Every singleton of a finite string is a neighbourhood of the binary-sequence system.

It is the second disjunct of the neighbourhood predicate, witnessed by its string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

theorem memC_singleton (σ : Str) : memC ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Example44
