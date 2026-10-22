/-ai
The operator associated with sets z and v sends a set w to the pointwise product of z with w, united with v.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- Scott's operator `w ↦ z·w ∪ v`, whose least fixed point is the least solution of `w = z·w ∪ v`. -/
def G (z v : Set S) (w : Set S) : Set S := z * w ∪ v

end DomainTheory.NeighbourhoodSystems.Exercise515
