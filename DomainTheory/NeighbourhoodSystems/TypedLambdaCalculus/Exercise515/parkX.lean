/-ai
Park's proposed solution for the first unknown is the pointwise product of the star of the feedback coefficient a ∪ b · a* · b with the feedback constant c ∪ b · a* · d.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkA
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- Park's least solution for `x`: `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`. -/
def parkX (a b c d : Set S) : Set S := star (parkA a b) * parkC a b c d

end DomainTheory.NeighbourhoodSystems.Exercise515
