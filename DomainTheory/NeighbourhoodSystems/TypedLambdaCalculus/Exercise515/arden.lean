/-ai
Arden's lemma: the least fixed point of the operator sending w to z · w ∪ v equals the pointwise product of the star of z with v.

The two inclusions are proved separately. The least-fixed-point comparison, applied to the fixed-point identity for that star product, gives one inclusion. For the other, an element of the star product belongs to any set that contains the value of the operator on itself, by the prefix lemma for the star product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_isFixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_subset_prefixed

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_least
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- **Arden's lemma.** The least solution of `w = z·w ∪ v` in `P S` is `z*·v`. (Stated via
`lfpSet`, Exercise 4.14; the proof uses neither `Monotone` nor `⋃` order lemmas, so it is
choice-free.) -/
theorem arden (z v : Set S) : lfpSet (G z v) = star z * v := by
  apply Set.Subset.antisymm
  · exact lfpSet_least (G z v) (star_mul_isFixed z v)
  · intro s hs x hx
    exact star_mul_subset_prefixed z v x hx hs

end DomainTheory.NeighbourhoodSystems.Exercise515
