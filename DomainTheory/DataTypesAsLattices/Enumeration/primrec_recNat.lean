/-ai
If a function v is primitive recursive, then its natural recursion code is primitive recursive.

Unfold the recursion code. It is the application of v to the numeral code of v, and application of codes and the numeral code are primitive recursive.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem primrec_recNat (v : ℕ → ℕ) (hv : Primrec v) :
    Primrec (recNat v) := by
  unfold recNat
  exact primrec_applyNat.comp hv (primrec_num.comp hv)

end DomainTheory.DataTypesAsLattices
