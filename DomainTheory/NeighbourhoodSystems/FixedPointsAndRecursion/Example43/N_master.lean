/-ai
The master neighbourhood of the natural-number system is the whole space of natural numbers.

The two sides agree by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

@[simp] theorem N_master : N.master = (Set.univ : Set ℕ) := rfl

end DomainTheory.NeighbourhoodSystems.Example43
