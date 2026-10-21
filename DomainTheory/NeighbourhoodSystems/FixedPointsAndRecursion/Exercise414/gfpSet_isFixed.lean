/-ai
The greatest fixed-point set of a monotone operator on subsets is a fixed point of that operator.

The set is contained in its image by the post-fixed-point inclusion for the greatest fixed-point set. The image is contained in the set because monotonicity makes the image a post-fixed point, and every post-fixed point is contained in the greatest fixed-point set. The two inclusions give equality.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.subset_gfpSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.gfpSet_subset_f

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}



/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is a fixed point: `f(g) = g`. -/
theorem gfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (gfpSet f) = gfpSet f := by
  have hsub : gfpSet f ⊆ f (gfpSet f) := gfpSet_subset_f f hf
  have hsup : f (gfpSet f) ⊆ gfpSet f := subset_gfpSet f (hf hsub)
  exact Set.Subset.antisymm hsup hsub

end DomainTheory.NeighbourhoodSystems.Exercise414
