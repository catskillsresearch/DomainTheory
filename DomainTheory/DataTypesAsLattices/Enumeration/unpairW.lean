/-ai
The least w such that k is less than the (w + 1)-st triangular number, computed by bounded recursion, is the bounded scan of k run for k steps.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Least `w` with `k < triangle (w+1)`, computed by bounded recursion. -/
def unpairW (k : ℕ) : ℕ := unpairWRec k k

end DomainTheory.DataTypesAsLattices
