module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.finiteBasisSups

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace CountablyAlgebraic

theorem compact_finite_support
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α)
    {m : ℕ} {x : Set ℕ}
    (h : D.compact m ≤ sSup (D.compact '' x)) :
    ∃ t : Finset ℕ, (t : Set ℕ) ⊆ x ∧
      D.compact m ≤ sSup (D.compact '' (t : Set ℕ)) := by
  have h' : D.compact m ≤ sSup (finiteBasisSups D.compact x) := by
    rwa [finiteBasisSups.sSup_eq]
  obtain ⟨y, ⟨t, htx, rfl⟩, hmy⟩ :=
    D.compact_isCompact m (finiteBasisSups D.compact x)
      (finiteBasisSups.directed D.compact x) h'
  exact ⟨t, htx, hmy⟩

end CountablyAlgebraic

end DomainTheory.DataTypesAsLattices
