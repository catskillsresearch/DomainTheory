/-ai
The closed conditional term avoids index 8.

Simplify by the definition of the term and the definition of avoidance.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem condClosed_avoids8 : condClosed.Avoids 8 := by
  simp [condClosed, Term.Avoids]

end DomainTheory.DataTypesAsLattices
