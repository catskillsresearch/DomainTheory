/-ai
The pairing combinator is the interpretation of the pairing term in the arithmetic environment.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pairComb : Pomega := interp pairTerm arithEnv

end DomainTheory.DataTypesAsLattices
