/-ai
The union of the unit with the two generators is contained in the image of every subset under the monoid power-set operator.

That union is the left-hand summand of the union that defines the operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.F

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- `{1} ∪ {a, b} ⊆ F a b x`. -/
theorem base_subset_F (a b : S) (x : Set S) : {1} ∪ {a, b} ⊆ F a b x :=
  Set.subset_union_left

end DomainTheory.NeighbourhoodSystems.Exercise417
