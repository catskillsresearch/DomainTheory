module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem eq_3_9_apply : applyNat 0 1 = 3 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
