module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.ContinuousBasis
public import DomainTheory.DataTypesAsLattices.FixedLattices.finiteBasisSups
public import DomainTheory.DataTypesAsLattices.FixedLattices.finiteBasisSups_directed
public import DomainTheory.DataTypesAsLattices.FixedLattices.sSup_finiteBasisSups

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem CountablyAlgebraic.compact_finite_support
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α)
    {m : ℕ} {x : Set ℕ}
    (h : D.compact m ≤ sSup (D.compact '' x)) :
    ∃ t : Finset ℕ, (t : Set ℕ) ⊆ x ∧
      D.compact m ≤ sSup (D.compact '' (t : Set ℕ)) := by
  have h' : D.compact m ≤ sSup (finiteBasisSups D.compact x) := by
    rwa [sSup_finiteBasisSups]
  obtain ⟨y, ⟨t, htx, rfl⟩, hmy⟩ :=
    D.compact_isCompact m (finiteBasisSups D.compact x)
      (finiteBasisSups_directed D.compact x) h'
  exact ⟨t, htx, hmy⟩

end DomainTheory.DataTypesAsLattices
