module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def finiteBasisSups {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) : Set α :=
  {y | ∃ t : Finset ℕ, (t : Set ℕ) ⊆ x ∧
    y = sSup (d '' (t : Set ℕ))}

end DomainTheory.DataTypesAsLattices
