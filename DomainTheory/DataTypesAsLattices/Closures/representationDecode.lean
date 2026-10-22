module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def representationDecode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : α :=
  sSup (D.compact '' x)

end DomainTheory.DataTypesAsLattices
