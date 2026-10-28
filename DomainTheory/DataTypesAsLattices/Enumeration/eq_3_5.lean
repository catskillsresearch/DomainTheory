module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.opNat
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem eq_3_5 (n m : ℕ) : opNat (pair n m) = n := by simp [opNat, unpair_pair]
end DomainTheory.DataTypesAsLattices
