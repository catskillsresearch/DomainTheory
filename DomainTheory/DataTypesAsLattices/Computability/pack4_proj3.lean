/-ai
The third projection of a fourfold pair packing is the first component of the unpairing of the second component of the unpairing of the second component.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pack4_proj3 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1

end DomainTheory.DataTypesAsLattices
