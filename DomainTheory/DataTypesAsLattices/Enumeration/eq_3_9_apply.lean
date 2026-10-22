/-ai
Scott 1976, (3.9), the application calculation: code application of 0 to 1 equals 3.

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


/-- **Scott 1976, (3.9).** `apply(0)(1) = 3` and `val(3) = ⟨suc,…⟩`. -/
theorem eq_3_9_apply : applyNat 0 1 = 3 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
