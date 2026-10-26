module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e

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
