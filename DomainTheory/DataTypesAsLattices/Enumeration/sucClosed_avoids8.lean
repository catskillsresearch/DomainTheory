/-ai
The closed successor term avoids the variable 8.

Unfolding the term and the avoidance predicate, the claim simplifies directly.
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


theorem sucClosed_avoids8 : sucClosed.Avoids 8 := by
  simp [sucClosed, Term.Avoids]

end DomainTheory.DataTypesAsLattices
