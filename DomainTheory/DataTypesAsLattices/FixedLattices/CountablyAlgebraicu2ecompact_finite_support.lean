/-ai
If a compact basis element of a countable algebraic lattice lies below the supremum of the basis elements indexed by a set, then some finite subset of that set already has the same basis element below the supremum of its basis elements.

The supremum of the indexed basis elements equals the supremum of the finite-basis suprema, so the hypothesis is a bound by that directed supremum. Compactness of the basis element extracts one finite-basis supremum, indexed by a finite set contained in the given set, that already lies above it.
ai-/
module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.Basic
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
