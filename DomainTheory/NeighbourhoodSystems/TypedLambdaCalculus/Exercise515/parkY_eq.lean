/-ai
Park's second component y₀ satisfies the equation y = b · x ∪ a · y ∪ d.

The fixed-point identity for the star product rewrites y₀ as a · y₀ united with (b · x₀ ∪ d). Reassociating and commuting the unions yields b · x₀ ∪ a · y₀ ∪ d.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_isFixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- `y₀` satisfies the second equation `y = b·x ∪ a·y ∪ d`. -/
theorem parkY_eq (a b c d : Set S) :
    parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d := by
  have hfix : a * parkY a b c d ∪ (b * parkX a b c d ∪ d) = parkY a b c d :=
    star_mul_isFixed a (b * parkX a b c d ∪ d)
  conv_lhs => rw [← hfix]
  simp only [Set.union_assoc, Set.union_comm]

end DomainTheory.NeighbourhoodSystems.Exercise515
