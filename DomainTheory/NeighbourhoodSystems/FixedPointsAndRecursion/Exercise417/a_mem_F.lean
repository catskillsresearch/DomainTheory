/-ai
The first generator belongs to the image of every subset under the monoid power-set operator.

It belongs to the union of the unit with the two generators, and that union is contained in the image.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
import all Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


theorem a_mem_F (a b : S) (x : Set S) : a ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_right _ (Set.mem_insert _ _))

end DomainTheory.NeighbourhoodSystems.Exercise417
