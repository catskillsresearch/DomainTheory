/-ai
The least fixed-point set of an operator on subsets is contained in every pre-fixed point.

A member of the least fixed-point set lies in every pre-fixed point, and the argument applies that property to the given pre-fixed point.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}


/-- `lfpSet f ⊆ x` for every pre-fixed point `f(x) ⊆ x`. -/
theorem lfpSet_subset (f : Set A → Set A) {x : Set A} (hx : f x ⊆ x) : lfpSet f ⊆ x :=
  fun _ ha => ha x hx

end DomainTheory.NeighbourhoodSystems.Exercise414
