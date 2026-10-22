module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (3.2).** `cond(x)(y)(0) = x`. -/
theorem eq_3_2 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) zeroC = x := by
  rw [condC_beta3]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using eq_2_7_zero x y

end DomainTheory.DataTypesAsLattices
