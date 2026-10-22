/-ai
The arithmetic environment sends index 0 to the addition combinator, index 1 to the multiplication combinator, index 2 to the subtraction combinator, and every other index to bottom.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def arithEnv : ℕ → Pomega
  | 0 => addC
  | 1 => mulC
  | 2 => subC
  | _ => botElem

end DomainTheory.DataTypesAsLattices
