module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def applyNat (n m : ℕ) : ℕ := pair n m + 1

end DomainTheory.DataTypesAsLattices
