module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Membership in `C₁`: a neighbourhood is a tail `tail n` or a singleton `{n}`. -/
def memC1 (X : Set ℕ) : Prop := (∃ n, X = tail n) ∨ (∃ n, X = {n})

end DomainTheory.NeighbourhoodSystems.Exercise425
