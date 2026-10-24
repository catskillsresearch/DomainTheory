module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.G
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkA
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ
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
