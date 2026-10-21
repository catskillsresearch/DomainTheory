/-ai
The value of code 1 is the zero combinator.

Code 1 equals the code application of 0 to 0. The value law for code application and the value of code 0 reduce the claim to the self-application of G.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_apply

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































theorem eq_3_8_val : valNat 1 = zeroC := by
  have : valNat 1 = valNat (applyNat 0 0) := by simp [eq_3_8_apply]
  rw [this, valNat_apply, valNat_zero, Gcomb_app_self]

end DomainTheory.DataTypesAsLattices
