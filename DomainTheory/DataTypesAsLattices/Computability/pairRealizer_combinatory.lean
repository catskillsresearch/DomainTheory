/-ai
If u and v are combinatory, then so is their pairing realizer.

It is S applied to S applied to K applied to the pairing combinator and to u, and then to v.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem pairRealizer_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (pairRealizer u v) :=
  .app (.app .S (.app (.app .S (.app .K pairComb_combinatory)) hu)) hv

end DomainTheory.DataTypesAsLattices
