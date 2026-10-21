/-ai
The diagonal intersection code of n is the code application of the code application of the intersection code to the numeral code of n, and then again to n. It is the primitive-recursive diagonal intersection code used in Theorem 3.4.
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
public import DomainTheory.DataTypesAsLattices.Enumeration.interCode

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- The primitive-recursive diagonal intersection code used in Theorem 3.4. -/
noncomputable def diagonalInterCode (n : ℕ) : ℕ :=
  applyNat (applyNat interCode (num n)) n

end DomainTheory.DataTypesAsLattices
