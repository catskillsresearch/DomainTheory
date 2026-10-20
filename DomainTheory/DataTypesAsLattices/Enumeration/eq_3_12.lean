module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_10_val

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, (3.12).** `val(num(n)) = n`. -/
theorem eq_3_12 : ∀ n, valNat (num n) = ofNat n
  | 0 => eq_3_8_val
  | n + 1 => by
    rw [num, valNat_apply, eq_3_10_val, eq_3_12, sucC_app, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
