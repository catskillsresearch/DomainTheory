module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.safePredC
public import DomainTheory.DataTypesAsLattices.Computability.pack4

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def subStepC : Pomega := funOf Kcomb safePredC

namespace subStepC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory subStepC :=
  .app .K safePredC.combinatory

end subStepC

end DomainTheory.DataTypesAsLattices
