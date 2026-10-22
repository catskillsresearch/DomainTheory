module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairSndC : Pomega := interp unpairSndTerm unpairEnv

end DomainTheory.DataTypesAsLattices
