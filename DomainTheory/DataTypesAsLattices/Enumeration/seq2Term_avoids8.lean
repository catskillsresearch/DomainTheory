/-ai
For any terms a and b, the term-level binary sequence constructor of a and b avoids the variable 8.

Avoidance holds by its first clause, which is definitionally the binding of 8.
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


theorem seq2Term_avoids8 (a b : Term) : (seq2Term a b).Avoids 8 :=
  Or.inl rfl

end DomainTheory.DataTypesAsLattices
