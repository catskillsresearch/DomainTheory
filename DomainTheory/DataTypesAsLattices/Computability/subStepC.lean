/-ai
The subtraction step subStepC is the K combinator applied to the safe predecessor safePredC, so the recursion step returns that predecessor independently of its counter argument.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.safePredC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def subStepC : Pomega := funOf Kcomb safePredC

end DomainTheory.DataTypesAsLattices
