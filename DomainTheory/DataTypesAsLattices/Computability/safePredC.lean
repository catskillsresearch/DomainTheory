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

/-- `λx. x ⊃ 0, x−1`, so numerals stay numerals. -/
def safePredC : Pomega :=
  interp (.lam 0 (.cond (.var 0) .zero (.pred (.var 0)))) (fun _ => botElem)

end DomainTheory.DataTypesAsLattices
