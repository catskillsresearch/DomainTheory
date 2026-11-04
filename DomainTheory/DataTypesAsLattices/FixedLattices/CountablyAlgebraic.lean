module

public import DomainTheory.DataTypesAsLattices.FixedLattices.IsCompact

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

structure CountablyAlgebraic (α : Type u) [CompleteLattice α] where
  compact : ℕ → α
  compact_isCompact : ∀ n, IsCompact (compact n)
  compact_complete : ∀ x, IsCompact x → ∃ n, x = compact n
  density : ∀ x, x = @sSup α completeLatticeSupSet
    {k : α | IsCompact k ∧ @LE.le α completeLatticeLE k x}

end DomainTheory.DataTypesAsLattices
