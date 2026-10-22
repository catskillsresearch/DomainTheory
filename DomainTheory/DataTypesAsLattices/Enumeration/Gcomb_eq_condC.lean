/-ai
The combinator G equals the application of the conditional to the packed combinators and then to zero.

This is the two-argument beta law for the conditional, read in reverse.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gcomb_eq_condC : Gcomb = funOf (funOf condC Gpack) zeroC :=
  (condC_beta2 Gpack zeroC).symm

end DomainTheory.DataTypesAsLattices
