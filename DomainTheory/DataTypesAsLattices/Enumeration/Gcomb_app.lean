/-ai
Applying G to an element z returns the conditional of z on the packed combinators and on zero.

This is the beta law for the graph of that conditional, which is Scott continuous in the tested argument.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gcomb_app (z : Pomega) :
    funOf Gcomb z = condSet z Gpack zeroC :=
  beta (condSet_isScottContinuous_left Gpack zeroC) z

end DomainTheory.DataTypesAsLattices
