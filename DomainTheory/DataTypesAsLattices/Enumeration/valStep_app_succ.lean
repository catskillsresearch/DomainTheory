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
