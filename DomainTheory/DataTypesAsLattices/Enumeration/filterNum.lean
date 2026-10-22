/-ai
The function filterNum sends a natural number q to one more than the second component of its unpairing when beforeHalt holds of the two unpaired components, and sends q to 0 otherwise.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def filterNum (q : ℕ) : ℕ :=
  if beforeHalt q.unpair.1 q.unpair.2 then q.unpair.2 + 1 else 0

end DomainTheory.DataTypesAsLattices
