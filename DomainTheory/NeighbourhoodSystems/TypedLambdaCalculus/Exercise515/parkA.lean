/-ai
The feedback coefficient of David Park's eliminated system, for coefficients a and b, is the union of a with the pointwise product b · a* · b.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- The "feedback" coefficient `A = a ∪ b·a*·b` of the eliminated system. -/
def parkA (a b : Set S) : Set S := a ∪ b * star a * b

end DomainTheory.NeighbourhoodSystems.Exercise515
