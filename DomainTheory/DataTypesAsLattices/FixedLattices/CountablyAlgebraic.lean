/-ai
A countable algebraic lattice on a complete lattice is an enumeration of elements such that every enumerated element is compact, every compact element equals some enumerated element, and every element is the supremum of the compact elements below it.
ai-/
module


public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsDirectedSet
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
