
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_Ycode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem theorem_3_3_val (n : ℕ) :
    valNat (recCode n) = funOf (valNat n) (valNat (recCode n)) := by
  rw [recCode, valNat_apply, valNat_Ycode]
  exact Ycomb_unfold (valNat n)

end DomainTheory.DataTypesAsLattices
