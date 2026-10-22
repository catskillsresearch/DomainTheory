/-ai
The value of code 12 is the successor combinator.

Code 12 equals the code application of 3 to 1. The value law for code application, together with the values of codes 3 and 1, reduces the claim to the application of the G-pack to the numeral 0, after identifying the zero combinator with that numeral.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_9_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_10_apply

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem eq_3_10_val : valNat 12 = sucC := by
  have : valNat 12 = valNat (applyNat 3 1) := by simp [eq_3_10_apply]
  rw [this, valNat_apply, eq_3_9_val, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gpack_zero

end DomainTheory.DataTypesAsLattices
