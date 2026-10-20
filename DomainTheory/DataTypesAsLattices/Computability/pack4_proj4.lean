module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pack4_proj4 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2

end DomainTheory.DataTypesAsLattices
