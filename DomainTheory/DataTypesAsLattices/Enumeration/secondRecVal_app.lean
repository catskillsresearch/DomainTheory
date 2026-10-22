/-ai
The second recursion value of u, applied to x, is the union over m in x of u applied to the numeral of apply(m)(num(m)).

This is the β-equation for that graph, whose continuity in the argument is the Scott continuity of the second recursion value.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem secondRecVal_app (u x : Pomega) :
    funOf (secondRecVal u) x =
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))) :=
  beta (secondRecVal_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
