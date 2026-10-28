
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

end DomainTheory.DataTypesAsLattices
