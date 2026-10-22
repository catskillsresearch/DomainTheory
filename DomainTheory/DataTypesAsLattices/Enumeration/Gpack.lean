module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Packed 5-tuple of the remaining combinators of Theorem 2.4. -/
def Gpack : Pomega :=
  seq2 sucC (seq2 predC (seq2 condC (seq2 Kcomb Scomb)))

end DomainTheory.DataTypesAsLattices
