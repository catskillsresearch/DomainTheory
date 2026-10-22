/-ai
Every set of indices is contained in its representing closure.

If an index belongs to the set, the corresponding compact element lies below the supremum of the compact elements indexed by the set, so the index belongs to the representing closure.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem representClosure_expansive {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    x ⊆ representClosure D x := by
  intro n hn
  exact le_sSup ⟨n, hn, rfl⟩

end DomainTheory.DataTypesAsLattices
