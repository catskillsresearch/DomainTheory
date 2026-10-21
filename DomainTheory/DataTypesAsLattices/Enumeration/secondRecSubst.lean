/-ai
The primitive recursive numerical substitution of Theorem 3.3 sends a natural number m to the application of m to the numeral of m.
ai-/

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

/-- The primitive-recursive numerical substitution used in Theorem 3.3. -/
def secondRecSubst (m : ℕ) : ℕ := applyNat m (num m)

end DomainTheory.DataTypesAsLattices
