module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

abbrev completeLatticeLE {α : Type u} [CompleteLattice α] : LE α :=
  @Preorder.toLE α
    (@PartialOrder.toPreorder α
      (@CompleteSemilatticeInf.toPartialOrder α
        (@CompleteLattice.toCompleteSemilatticeInf α ‹_›)))

end DomainTheory.DataTypesAsLattices
