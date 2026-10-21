/-ai
The shifted enumerator of the halting set sends t to one more than the first component of its unpairing when step-bounded evaluation, for the number of steps given by the second component, of the code decoded from the first component on input 0 returns a value, and sends t to 0 otherwise. The value 0 is the miss marker.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Shifted enumerator of the halting set: `0` is the miss marker. -/
def haltEnum (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome
    then t.unpair.1 + 1 else 0

end DomainTheory.DataTypesAsLattices
