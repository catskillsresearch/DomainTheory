/-ai
The greatest fixed-point set of a monotone operator on subsets is a post-fixed point: it is contained in its image.

An element of the greatest fixed-point set belongs to some post-fixed point. That point is contained in the greatest fixed-point set, so monotonicity places its image inside the image of the greatest fixed-point set, and the element lies in the image of the point.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
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
