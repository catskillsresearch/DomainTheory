module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem eq_3_6 (n m : ℕ) : argNat (pair n m) = m := by simp [argNat, unpair_pair]

end DomainTheory.DataTypesAsLattices
