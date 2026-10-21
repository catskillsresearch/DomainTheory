/-ai
The environment primRecOpEnv is the curried operator sending an initial value and a step to primRecComb of those arguments. It returns the application combinator dollarC at index 2, the fixed-point combinator Ycomb at index 3, the interpretation of primRecStepTerm in the constantly bottom environment at index 4, and the bottom element at every other index.
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

/-- Curried operator `λa f. primRecComb a f`. -/
def primRecOpEnv : ℕ → Pomega
  | 2 => dollarC
  | 3 => Ycomb
  | 4 => interp primRecStepTerm (fun _ => botElem)
  | _ => botElem

end DomainTheory.DataTypesAsLattices
