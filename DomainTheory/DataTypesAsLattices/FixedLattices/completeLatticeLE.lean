module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Pin `≤` / `sSup` to the `CompleteLattice` instance path so Challenge and
Solution elaborate `CountablyAlgebraic.mk` identically. -/
abbrev completeLatticeLE {α : Type u} [CompleteLattice α] : LE α :=
  @Preorder.toLE α
    (@PartialOrder.toPreorder α
      (@CompleteSemilatticeInf.toPartialOrder α
        (@CompleteLattice.toCompleteSemilatticeInf α ‹_›)))

end DomainTheory.DataTypesAsLattices
