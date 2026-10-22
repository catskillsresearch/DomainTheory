/-ai
The environment unpairEnv returns the square-root combinator sqrtC at index 1, the subtraction combinator subC at index 2, the multiplication combinator mulC at index 3, the comparison combinator leC at index 4, and the bottom element at every other index.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC

@[expose] public section

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
