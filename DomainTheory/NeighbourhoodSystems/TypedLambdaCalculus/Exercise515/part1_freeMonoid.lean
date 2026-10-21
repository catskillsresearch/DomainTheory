/-ai
On the free monoid of binary words, the least fixed point of the map sending w to {e} · w ∪ {e'} equals the product of the star of {e} with {e'}.

This is the single-equation law of the first part, applied in that monoid.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.part1

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]









/-- The free semigroup `{0,1}*` of the exercise. Part (1) holds here as a special case. -/
theorem part1_freeMonoid (e e' : FreeMonoid Bool) :
    lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'})
      = star ({e} : Set (FreeMonoid Bool)) * {e'} :=
  part1 e e'

end DomainTheory.NeighbourhoodSystems.Exercise515
