
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
