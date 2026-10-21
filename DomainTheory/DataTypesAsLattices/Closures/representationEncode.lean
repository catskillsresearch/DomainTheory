/-ai
Encoding an element of a countably algebraic lattice is the set of indices whose compact element lies below that element.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def representationEncode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : α) : Pomega :=
  {n | D.compact n ≤ x}

end DomainTheory.DataTypesAsLattices
