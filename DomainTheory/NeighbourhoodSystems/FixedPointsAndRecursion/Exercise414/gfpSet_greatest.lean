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



/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is the *greatest* fixed point: any fixed
point `y = f(y)` satisfies `y ⊆ g`. Hence `f` *does* have a maximum fixed point. -/
theorem gfpSet_greatest (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    y ⊆ gfpSet f := subset_gfpSet f (le_of_eq hy.symm)

end DomainTheory.NeighbourhoodSystems.Exercise414
