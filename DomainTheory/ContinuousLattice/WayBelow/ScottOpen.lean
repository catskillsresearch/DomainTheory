module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, §2, the induced topology.** `U` is *Scott-open* when it is an upper set and
is inaccessible by suprema of non-empty directed sets: if a non-empty directed `S` has its
supremum in `U`, then some member of `S` already lies in `U`. -/
def ScottOpen (U : Set D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D :=
    (CompleteLattice.toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

end DomainTheory.ContinuousLattice
