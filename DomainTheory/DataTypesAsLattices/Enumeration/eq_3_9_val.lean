module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_9_apply
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem eq_3_9_val : valNat 3 = Gpack := by
  have : valNat 3 = valNat (applyNat 0 1) := by simp [eq_3_9_apply]
  rw [this, valNat.app, valNat.zero, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gcomb.zero

end DomainTheory.DataTypesAsLattices
