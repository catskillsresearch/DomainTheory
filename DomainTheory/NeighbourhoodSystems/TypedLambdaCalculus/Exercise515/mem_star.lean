/-ai
A point lies in the star of a set if and only if it lies in some finite pointwise power of that set.

The two sides are the same by definition of the star.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


theorem mem_star {z : Set S} {s : S} : s ∈ star z ↔ ∃ n, s ∈ kpow z n := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise515
