/-ai
If r is combinatory, then so is its range enumerator.

The enumerator is the application of the dollar combinator to r and then to the top element.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.topElem_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem enumRangeC_combinatory {r : Pomega} (hr : IsCombinatory r) :
    IsCombinatory (enumRangeC r) :=
  .app (.app dollarC_combinatory hr) topElem_combinatory

end DomainTheory.DataTypesAsLattices
