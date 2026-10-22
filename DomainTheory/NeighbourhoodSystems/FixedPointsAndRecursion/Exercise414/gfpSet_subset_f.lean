module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.subset_gfpSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}


/-- `gfpSet f ⊆ f (gfpSet f)`: it is a post-fixed point. -/
theorem gfpSet_subset_f (f : Set A → Set A) (hf : Monotone f) :
    gfpSet f ⊆ f (gfpSet f) := by
  rintro a ⟨x, hx, hax⟩
  exact hf (subset_gfpSet f hx) (hx hax)

end DomainTheory.NeighbourhoodSystems.Exercise414
