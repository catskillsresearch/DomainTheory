module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

abbrev completeLatticePreorder {α : Type u} [CompleteLattice α] : Preorder α :=
  @PartialOrder.toPreorder α
    (@CompleteSemilatticeInf.toPartialOrder α
      (@CompleteLattice.toCompleteSemilatticeInf α ‹_›))

end DomainTheory.DataTypesAsLattices
