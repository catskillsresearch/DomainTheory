/-ai
The value of the recursion code of n equals the value of n applied to the value of that same recursion code.

Rewrite the recursion code as application of the Y-code, use the application equation for val and the value of the Y-code, and apply the unfolding equation of the Y combinator to val(n).
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
