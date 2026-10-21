/-ai
The least fixed-point set of an operator on subsets is contained in every fixed point.

A fixed point satisfies the pre-fixed inclusion, and the least fixed-point set is contained in every pre-fixed point.
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





/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is the *least* fixed point: any fixed
point `y = f(y)` satisfies `b ⊆ y`. -/
theorem lfpSet_least (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    lfpSet f ⊆ y := lfpSet_subset f (le_of_eq hy)

end DomainTheory.NeighbourhoodSystems.Exercise414
