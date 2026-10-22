module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pack4_proj2 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair t).2).1

end DomainTheory.DataTypesAsLattices
