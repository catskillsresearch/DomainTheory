/-ai
The combinator S equals G applied to the zero combinator and then four times to the numeral 1.

Identify the zero combinator with the numeral 0, and simplify by the zero application of G, the application of the G-pack to the numeral 1, and three uses of sequencing applied to the numeral 1.
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

theorem Scomb_from_G :
    Scomb =
      funOf (funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        (ofNat 1)) (ofNat 1) := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_one, seq2_app_one]

end DomainTheory.DataTypesAsLattices
