module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.WayBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Compactness internal to a complete lattice. -/
def IsCompact {α : Type u} [CompleteLattice α] (x : α) : Prop :=
  WayBelow x x

end DomainTheory.DataTypesAsLattices
