/-ai
The predecessor combinator equals the application of G to the zero combinator, then to the numeral 1, then again to the zero combinator.

The zero combinator is the numeral 0. Simplify by the zero law for G, the one law for the packed combinator, and the zero law for binary sequencing.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_one

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem predC_from_G :
    predC = funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_zero]

end DomainTheory.DataTypesAsLattices
