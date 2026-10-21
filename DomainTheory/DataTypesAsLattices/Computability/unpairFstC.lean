/-ai
The element unpairFstC is the interpretation of the first-projection term unpairFstTerm in the unpairing environment unpairEnv.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairFstC : Pomega := interp unpairFstTerm unpairEnv

end DomainTheory.DataTypesAsLattices
