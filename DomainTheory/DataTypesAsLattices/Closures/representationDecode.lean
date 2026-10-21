/-ai
Decoding a set of indices in a countably algebraic lattice is the supremum of the compact elements indexed by that set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def representationDecode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : α :=
  sSup (D.compact '' x)

end DomainTheory.DataTypesAsLattices
