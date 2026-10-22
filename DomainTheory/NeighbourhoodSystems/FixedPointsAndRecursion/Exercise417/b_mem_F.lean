/-ai
The second generator belongs to the image of every subset under the monoid power-set operator.

It belongs to the union of the unit with the two generators, and that union is contained in the image.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


theorem b_mem_F (a b : S) (x : Set S) : b ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl))

end DomainTheory.NeighbourhoodSystems.Exercise417
