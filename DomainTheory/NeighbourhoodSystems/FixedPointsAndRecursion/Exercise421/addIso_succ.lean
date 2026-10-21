/-ai
The addition equivalence preserves successor: the image of n + 1 under addition by m is one more than the image of n.

Rewrite both sides by the addition formula and compare the resulting sums by arithmetic.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.addIso_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414









/-- The isomorphism preserves the successor: `addIso m (n⁺) = (addIso m n)⁺`. -/
theorem addIso_succ (m n : ℕ) : (addIso m (n + 1) : ℕ) = (addIso m n : ℕ) + 1 := by
  simp only [addIso_apply]; omega

end DomainTheory.NeighbourhoodSystems.Exercise421
