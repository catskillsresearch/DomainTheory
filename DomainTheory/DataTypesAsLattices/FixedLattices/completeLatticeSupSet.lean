module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

abbrev completeLatticeSupSet {α : Type u} [CompleteLattice α] : SupSet α :=
  @CompleteSemilatticeSup.toSupSet α
    (@CompleteLattice.toCompleteSemilatticeSup α ‹_›)

end DomainTheory.DataTypesAsLattices
