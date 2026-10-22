module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
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
