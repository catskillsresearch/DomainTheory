/-ai
Scott 1976, (3.11). The numeral code sends 0 to 1, and sends n + 1 to the application of code 12 to the numeral code of n.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.11).** `num(0) = 1`, `num(n+1) = apply(12, num n)`. -/
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

end DomainTheory.DataTypesAsLattices
