/-ai
The successor combinator equals G applied to zero and then to zero again. The six constants are recovered from G and 0 by projection.

Zero is definitionally the numeral 0. Simplifying by the zero equation for G and the zero equation for the packed generator yields the successor.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_zero

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- The six constants are recovered from `G` and `0` by projection. -/
theorem sucC_from_G : sucC = funOf (funOf Gcomb zeroC) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_zero]

end DomainTheory.DataTypesAsLattices
