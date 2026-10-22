module


public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.WayBelow
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeLE
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeSupSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticePreorder

@[expose] public section

namespace DomainTheory.DataTypesAsLattices


/-- A concrete countable algebraic lattice: `compact` enumerates exactly the
compact elements and `density` says that they generate every point. -/
structure CountablyAlgebraic (α : Type u) [CompleteLattice α] where
  compact : ℕ → α
  compact_isCompact : ∀ n, IsCompact (compact n)
  compact_complete : ∀ x, IsCompact x → ∃ n, x = compact n
  density : ∀ x, x = @sSup α completeLatticeSupSet
    {k : α | IsCompact k ∧ @LE.le α completeLatticeLE k x}

end DomainTheory.DataTypesAsLattices
