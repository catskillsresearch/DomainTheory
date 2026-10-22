/-ai
The primitive-recursion combinator of elements f and g is the interpretation of the primitive-recursion term in the environment determined by f and g.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.precEnv
public import DomainTheory.DataTypesAsLattices.Computability.precTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def precC (f g : Pomega) : Pomega := interp precTerm (precEnv f g)

end DomainTheory.DataTypesAsLattices
