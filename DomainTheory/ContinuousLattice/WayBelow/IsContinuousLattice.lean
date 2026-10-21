/-ai
Scott 1972, Definition 2.3. A complete lattice is a continuous lattice when every element is the least upper bound of the set of elements way below it.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic.notation5

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, Definition 2.3.** A complete lattice `D` is a *continuous lattice* when every
element is the supremum of the elements way below it: `y = ⊔ {x | x ≪ y}`. -/
def IsContinuousLattice (D : Type u) [CompleteLattice D] : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  ∀ y : D, IsLUB {x | x ≪ y} y

end DomainTheory.ContinuousLattice
