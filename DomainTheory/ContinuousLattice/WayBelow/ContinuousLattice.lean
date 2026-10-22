module

public import DomainTheory.ContinuousLattice.WayBelow.Basic.notation5

@[expose] public section

namespace DomainTheory

open scoped DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

class ContinuousLattice (D : Type u) [CompleteLattice D] : Prop where
  out : letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
    ∀ y : D, IsLUB {x | x ≪ y} y
  /-- In a continuous lattice, `y` is the supremum of `{x | x ≪ y}`. -/
  sSup_wayBelow : ∀ y : D, sSup {x | x ≪ y} = y := fun y => (out y).sSup_eq

end DomainTheory
