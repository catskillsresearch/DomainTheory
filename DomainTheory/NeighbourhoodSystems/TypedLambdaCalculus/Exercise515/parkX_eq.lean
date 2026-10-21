/-ai
Park's first component x₀ satisfies the equation x = a · x ∪ b · y ∪ c, with y the accompanying component.

The fixed-point identity for the star product rewrites x₀ as the product of the feedback coefficient with x₀, united with the feedback constant. Expanding those two sets and the accompanying component, and simplifying by both distributivity laws, associativity of the product, and commutation of unions, yields a · x₀ ∪ b · y₀ ∪ c.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_assoc
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.sunion_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_union
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_isFixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]














/-- `x₀` satisfies the first equation `x = a·x ∪ b·y ∪ c`. -/
theorem parkX_eq (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c := by
  have hfix : parkA a b * parkX a b c d ∪ parkC a b c d = parkX a b c d :=
    star_mul_isFixed (parkA a b) (parkC a b c d)
  conv_lhs => rw [← hfix]
  simp only [parkA, parkC, parkY, sunion_mul, smul_union, smul_assoc,
    Set.union_comm, Set.union_left_comm]

end DomainTheory.NeighbourhoodSystems.Exercise515
