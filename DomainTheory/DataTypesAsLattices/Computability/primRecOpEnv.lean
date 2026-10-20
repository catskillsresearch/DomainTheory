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

/-- Curried operator `λa f. primRecComb a f`. -/
def primRecOpEnv : ℕ → Pomega
  | 2 => dollarC
  | 3 => Ycomb
  | 4 => interp primRecStepTerm (fun _ => botElem)
  | _ => botElem

end DomainTheory.DataTypesAsLattices
