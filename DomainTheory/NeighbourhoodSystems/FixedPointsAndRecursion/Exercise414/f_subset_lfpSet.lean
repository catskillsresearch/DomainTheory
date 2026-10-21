/-ai
The image under a monotone endomap f of the intersection of the pre-fixed points is contained in that intersection.

An element of the image, tested against a pre-fixed point x, lies in f(x) because monotonicity and the containment of the intersection in x put the image inside f(x), and the pre-fixed-point inclusion then puts it in x.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_subset

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}


/-- `f (lfpSet f) ⊆ lfpSet f`: it is a pre-fixed point. -/
theorem f_subset_lfpSet (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) ⊆ lfpSet f := by
  intro a ha x hx
  exact hx (hf (lfpSet_subset f hx) ha)

end DomainTheory.NeighbourhoodSystems.Exercise414
