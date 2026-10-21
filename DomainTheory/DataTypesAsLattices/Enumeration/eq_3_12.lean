/-ai
Scott 1976, (3.12): for every natural number n, the value of the numeral code of n is the numeral n.

The case n = 0 is the value of code 1. For a successor, rewrite the numeral code by its definition and the value law for code application, use that the value of code 12 is the successor combinator together with the inductive hypothesis, and finish by the application law for the successor and the successor of a numeral.
ai-/
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
