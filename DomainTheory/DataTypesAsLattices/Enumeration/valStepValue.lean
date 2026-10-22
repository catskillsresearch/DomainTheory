module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- The application selected by one positive Gödel code. -/
def valStepValue (v : Pomega) : ℕ → Pomega
  | 0 => botElem
  | p + 1 =>
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2))

end DomainTheory.DataTypesAsLattices
