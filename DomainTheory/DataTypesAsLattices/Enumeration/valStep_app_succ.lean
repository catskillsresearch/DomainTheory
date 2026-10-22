/-ai
Applying the enumerator step at v to the numeral of p + 1 equals the application of v at the numeral of the left unpairing component of p to the application of v at the numeral of the right component.

Rewrite by the application law for the step and by equation (2.7) at a successor, then simplify the minimal extension, the selected application, and the numeral.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem valStep_app_succ (v : Pomega) (p : ℕ) :
    funOf (valStep v) (ofNat (p + 1)) =
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2)) := by
  rw [valStep_app, eq_2_7_succ]
  simp [minExtend, valStepValue, ofNat]

end DomainTheory.DataTypesAsLattices
