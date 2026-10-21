/-ai
Scott 1976, (3.10), the application calculation: code application of 3 to 1 equals 12.

Simplify by the definition of code application and by pairing.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (3.10).** `apply(3)(1) = 12` and `val(12) = suc`. -/
theorem eq_3_10_apply : applyNat 3 1 = 12 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
