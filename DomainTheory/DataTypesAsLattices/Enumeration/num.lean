module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

end DomainTheory.DataTypesAsLattices
