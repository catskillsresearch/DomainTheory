/-ai
Every post-fixed point of an operator on subsets is contained in the greatest fixed-point set.

An element of a post-fixed point is entered in the greatest fixed-point set together with that point and the post-fixed inclusion.
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


/-- Every post-fixed point `x ⊆ f(x)` is contained in `gfpSet f`. -/
theorem subset_gfpSet (f : Set A → Set A) {x : Set A} (hx : x ⊆ f x) : x ⊆ gfpSet f :=
  fun _ ha => ⟨x, hx, ha⟩

end DomainTheory.NeighbourhoodSystems.Exercise414
