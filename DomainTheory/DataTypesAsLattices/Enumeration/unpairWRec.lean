/-ai
The bounded scan for the least w such that k is less than the (w + 1)-st triangular number, run for n steps, starts at 0 and at stage w returns the previous value when k is already below the (w + 1)-st triangular number, and otherwise returns w + 1.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Bounded scan for the least `w` with `k < triangle (w+1)`. -/
def unpairWRec (k n : ℕ) : ℕ :=
  Nat.rec 0 (fun w ih => if k < triangle (w + 1) then ih else w + 1) n

end DomainTheory.DataTypesAsLattices
