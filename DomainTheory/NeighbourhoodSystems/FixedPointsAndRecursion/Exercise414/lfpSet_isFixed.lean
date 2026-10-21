/-ai
The least fixed-point set of a monotone operator on subsets is a fixed point of that operator.

The image is contained in the set by the pre-fixed-point inclusion for the least fixed-point set. The set is contained in its image because monotonicity makes the image a pre-fixed point, and the least fixed-point set is contained in every pre-fixed point. The two inclusions give equality.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_subset
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.f_subset_lfpSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}


/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is a fixed point: `f(b) = b`. -/
theorem lfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) = lfpSet f := by
  have hsub : f (lfpSet f) ⊆ lfpSet f := f_subset_lfpSet f hf
  have hsup : lfpSet f ⊆ f (lfpSet f) := lfpSet_subset f (hf hsub)
  exact Set.Subset.antisymm hsub hsup

end DomainTheory.NeighbourhoodSystems.Exercise414
