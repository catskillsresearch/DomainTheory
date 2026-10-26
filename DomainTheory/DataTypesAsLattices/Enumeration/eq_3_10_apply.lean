module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (3.10).** `apply(3)(1) = 12` and `val(12) = suc`. -/
theorem eq_3_10_apply : applyNat 3 1 = 12 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
