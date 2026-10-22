/-ai
Every singleton is a unary neighbourhood.

It is the singleton clause of the neighbourhood predicate at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem memC1_singleton (n : ℕ) : memC1 ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise425
