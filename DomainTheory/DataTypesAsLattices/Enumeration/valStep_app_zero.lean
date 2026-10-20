module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



























theorem valStep_app_zero (v : Pomega) :
    funOf (valStep v) (ofNat 0) = Gcomb := by
  rw [valStep_app]
  exact eq_2_7_zero Gcomb (minExtend (valStepValue v) (ofNat 0))

end DomainTheory.DataTypesAsLattices
