/-ai
In a continuous lattice, an element equals the supremum of the elements way below it.

The continuous-lattice hypothesis says that the element is the least upper bound of that set, and a least upper bound equals the supremum.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]





/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`. -/
theorem IsContinuousLattice.sSup_wayBelow (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h y).sSup_eq

end DomainTheory.ContinuousLattice
