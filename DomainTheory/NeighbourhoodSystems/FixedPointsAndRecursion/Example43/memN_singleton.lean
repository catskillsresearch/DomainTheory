/-ai
Every singleton of a natural number is a neighbourhood of the natural-number system.

It is the second disjunct of the neighbourhood predicate, witnessed by its element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem memN_singleton (n : ℕ) : memN ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Example43
