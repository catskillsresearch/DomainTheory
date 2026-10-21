/-ai
The environment for the primitive-recursion constructor of the primitive recursive functions sends index 3 to the recursion operator, index 4 to f, index 5 to g, index 6 to the first unpairing combinator, index 7 to the second unpairing combinator, index 8 to the pairing combinator, and every other index to bottom.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Environment for the primitive-recursion constructor of `Nat.Primrec`. -/
def precEnv (f g : Pomega) : ℕ → Pomega
  | 3 => primRecOpC
  | 4 => f
  | 5 => g
  | 6 => unpairFstC
  | 7 => unpairSndC
  | 8 => pairComb
  | _ => botElem

end DomainTheory.DataTypesAsLattices
