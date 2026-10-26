module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def filterNum (q : ℕ) : ℕ :=
  if beforeHalt q.unpair.1 q.unpair.2 then q.unpair.2 + 1 else 0

end DomainTheory.DataTypesAsLattices
