/-ai
In a continuous lattice, an element equals the supremum of the elements way below it.

The continuous-lattice hypothesis says that the element is the least upper bound of that set, and a least upper bound equals the supremum.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`. -/
theorem sSup_wayBelow (h : ContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h.out y).sSup_eq

end DomainTheory.ContinuousLattice
