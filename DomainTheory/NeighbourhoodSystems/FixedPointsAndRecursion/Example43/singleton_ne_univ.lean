/-ai
A singleton of a natural number is not the whole space.

An equality the other way would contradict the inequality of the whole space with that singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- `{n} ≠ ℕ` (the symmetric form). -/
theorem singleton_ne_univ (n : ℕ) : ({n} : Set ℕ) ≠ Set.univ := fun h => univ_ne_singleton n h.symm

end DomainTheory.NeighbourhoodSystems.Example43
