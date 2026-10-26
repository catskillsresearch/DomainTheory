module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def enumRangeC (r : Pomega) : Pomega :=
  (dollarC ⬝ r) ⬝ topElem

end DomainTheory.DataTypesAsLattices
