/-ai
The Myhill realizer of any function is Scott continuous.

It is an application map, and application is Scott continuous.
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




































































theorem myhillRealizer_isScottContinuous (p : ℕ → ℕ) :
    IsScottContinuous (myhillRealizer p) :=
  funOf_isScottContinuous _

end DomainTheory.DataTypesAsLattices
