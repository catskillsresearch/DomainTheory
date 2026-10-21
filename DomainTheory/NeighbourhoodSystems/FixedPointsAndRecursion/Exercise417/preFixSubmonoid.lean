/-ai
A pre-fixed point of the monoid power-set operator is the carrier of a submonoid. The unit belongs to the image and hence to the set, and the product of two members belongs to the pointwise square, hence to the image, and hence to the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
import all Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.self_mul_subset_F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.one_mem_F

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- A pre-fixed point of `F` is a submonoid containing `{a, b}`: it contains `1` and is closed under
multiplication and contains `a, b`. Packaged as the submonoid with that carrier. -/
def preFixSubmonoid (a b : S) {x : Set S} (hx : F a b x ⊆ x) : Submonoid S where
  carrier := x
  one_mem' := hx (one_mem_F a b x)
  mul_mem' := by
    intro s t hs ht
    exact hx (self_mul_subset_F a b x (Set.mul_mem_mul hs ht))

end DomainTheory.NeighbourhoodSystems.Exercise417
