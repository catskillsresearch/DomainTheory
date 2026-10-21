/-ai
The closed predecessor term avoids index 8.

Simplify the avoidance predicate on the definition of the term.
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




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

























































theorem predClosed_avoids8 : predClosed.Avoids 8 := by
  simp [predClosed, Term.Avoids]

end DomainTheory.DataTypesAsLattices
