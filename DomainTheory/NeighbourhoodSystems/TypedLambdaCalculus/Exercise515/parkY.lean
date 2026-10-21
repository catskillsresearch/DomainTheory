/-ai
The accompanying component of Park's solution is the pointwise product of the star of a with the union of b · x₀ and d.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- The accompanying least solution for `y`: `y₀ = a*·(b·x₀ ∪ d)`. -/
def parkY (a b c d : Set S) : Set S := star a * (b * parkX a b c d ∪ d)

end DomainTheory.NeighbourhoodSystems.Exercise515
