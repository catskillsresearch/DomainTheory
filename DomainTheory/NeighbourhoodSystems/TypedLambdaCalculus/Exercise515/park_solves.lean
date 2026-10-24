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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkY_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- **Exercise 5.15(2), existence.** `(x₀, y₀)` solves David Park's system. -/
theorem park_solves (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
      parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d :=
  ⟨parkX_eq a b c d, parkY_eq a b c d⟩

end DomainTheory.NeighbourhoodSystems.Exercise515
