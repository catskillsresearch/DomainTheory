/-ai
Applying the enumerator step at v to the numeral of zero equals the G combinator.

Rewrite by the application law for the step, and apply equation (2.7) at zero to the G combinator and the minimal extension of the selected application.
ai-/
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
