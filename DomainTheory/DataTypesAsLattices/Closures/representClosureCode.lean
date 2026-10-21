/-ai
The code of the representing closure is the graph of the representing closure operation.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The `Pω` code of the representing closure operation. -/
def representClosureCode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) : Pomega :=
  graph (representClosure D)

end DomainTheory.DataTypesAsLattices
