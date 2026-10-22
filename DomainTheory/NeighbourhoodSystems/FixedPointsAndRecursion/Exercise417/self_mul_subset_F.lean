/-ai
The pointwise square of a subset is contained in its image under the monoid power-set operator.

The square is the right-hand summand of the union that defines the operator.
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

theorem self_mul_subset_F (a b : S) (x : Set S) : x * x ⊆ F a b x :=
  Set.subset_union_right

end DomainTheory.NeighbourhoodSystems.Exercise417
