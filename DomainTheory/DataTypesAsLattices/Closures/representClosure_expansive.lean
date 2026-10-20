module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
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
