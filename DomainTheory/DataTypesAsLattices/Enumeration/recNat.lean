module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.3 (ii).** `rec(n) = apply(v(n))(num(v(n)))`. -/
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

end DomainTheory.DataTypesAsLattices
