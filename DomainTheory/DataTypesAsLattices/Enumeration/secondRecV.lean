/-ai
Scott's primitive recursive function v of Theorem 3.3 sends n to the application of the second recursion operator code to n.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperatorCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Scott's primitive-recursive function `v` in Theorem 3.3. -/
noncomputable def secondRecV (n : ℕ) : ℕ :=
  applyNat secondRecOperatorCode n

end DomainTheory.DataTypesAsLattices
