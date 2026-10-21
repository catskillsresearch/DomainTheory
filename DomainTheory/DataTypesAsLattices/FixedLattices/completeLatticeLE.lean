/-ai
The abbreviation completeLatticeLE selects the order of a complete lattice by following the instance through the complete-semilattice infimum, the partial order, and the preorder. The path is fixed so that the two elaborations of a countable algebraic lattice use the same order.
ai-/
module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Pin `≤` / `sSup` to the `CompleteLattice` instance path so Challenge and
Solution elaborate `CountablyAlgebraic.mk` identically. -/
abbrev completeLatticeLE {α : Type u} [CompleteLattice α] : LE α :=
  @Preorder.toLE α
    (@PartialOrder.toPreorder α
      (@CompleteSemilatticeInf.toPartialOrder α
        (@CompleteLattice.toCompleteSemilatticeInf α ‹_›)))

end DomainTheory.DataTypesAsLattices
