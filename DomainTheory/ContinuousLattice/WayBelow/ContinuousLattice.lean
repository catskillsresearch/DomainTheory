module

public import DomainTheory.ContinuousLattice.WayBelow.Basic.notation5

@[expose] public section

namespace DomainTheory

open scoped DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, Definition 2.3.** A complete lattice `D` is a *continuous lattice* when every
element is the supremum of the elements way below it: `y = ⊔ {x | x ≪ y}`. -/
class ContinuousLattice (D : Type u) [CompleteLattice D] : Prop where
  out : letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
    ∀ y : D, IsLUB {x | x ≪ y} y

end DomainTheory
