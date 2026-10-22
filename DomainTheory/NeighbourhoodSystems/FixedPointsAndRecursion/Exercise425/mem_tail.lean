/-ai
A natural lies in the tail of length n if and only if n is at most that natural.

The equivalence is the definition of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

@[simp] theorem mem_tail {n k : ℕ} : k ∈ tail n ↔ n ≤ k := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise425
