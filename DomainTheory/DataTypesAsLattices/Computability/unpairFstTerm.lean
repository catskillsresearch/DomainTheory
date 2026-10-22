module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairTestTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairFstTerm : Term :=
  .lam 0 (.cond unpairTestTerm unpairSqrtTerm unpairDeltaTerm)

end DomainTheory.DataTypesAsLattices
