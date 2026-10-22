/-ai
The successor power of a set equals the pointwise product of the set with the preceding power.

This is the successor clause of the definition of the powers, by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

@[simp] theorem kpow_succ (z : Set S) (n : ℕ) : kpow z (n + 1) = z * kpow z n := rfl

end DomainTheory.NeighbourhoodSystems.Exercise515
