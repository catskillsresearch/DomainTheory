module

public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

def WayBelow (x y : D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : Preorder D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

end DomainTheory.ContinuousLattice
