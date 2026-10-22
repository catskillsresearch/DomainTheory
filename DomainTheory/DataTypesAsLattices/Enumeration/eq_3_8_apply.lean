/-ai
Scott 1976, (3.8), the application calculation: code application of 0 to 0 equals 1.

Simplify by the definition of code application and by pairing.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (3.8).** `apply(0)(0) = 1` and `val(1) = 0`. -/
theorem eq_3_8_apply : applyNat 0 0 = 1 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
