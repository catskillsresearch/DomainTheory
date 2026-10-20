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

def pack4 (n0 n1 n2 m : ℕ) : ℕ :=
  Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m))

end DomainTheory.DataTypesAsLattices
