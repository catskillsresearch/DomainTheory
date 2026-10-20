module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_9_apply

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































theorem eq_3_9_val : valNat 3 = Gpack := by
  have : valNat 3 = valNat (applyNat 0 1) := by simp [eq_3_9_apply]
  rw [this, valNat_apply, valNat_zero, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gcomb_zero

end DomainTheory.DataTypesAsLattices
