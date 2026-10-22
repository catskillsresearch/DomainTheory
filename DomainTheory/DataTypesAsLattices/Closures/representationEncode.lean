module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def representationEncode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : α) : Pomega :=
  {n | D.compact n ≤ x}

end DomainTheory.DataTypesAsLattices
