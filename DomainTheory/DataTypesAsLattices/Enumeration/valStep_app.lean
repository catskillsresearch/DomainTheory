/-ai
Applying the enumerator step at v to a code k equals the McCarthy conditional of k, with zero branch the G combinator and positive branch the minimal extension of the application selected by v at k.

This is the beta law for the Scott-continuous body of the enumerator step at v.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_body_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem valStep_app (v k : Pomega) :
    funOf (valStep v) k =
      condSet k Gcomb (minExtend (valStepValue v) k) :=
  beta (valStep_body_isScottContinuous v) k

end DomainTheory.DataTypesAsLattices
