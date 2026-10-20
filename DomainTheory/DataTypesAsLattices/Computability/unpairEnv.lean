module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairEnv : ℕ → Pomega
  | 1 => sqrtC
  | 2 => subC
  | 3 => mulC
  | 4 => leC
  | _ => botElem

end DomainTheory.DataTypesAsLattices
