module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def addStepC : Pomega := funOf Kcomb sucC

namespace addStepC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory addStepC :=
  .app .K .suc

end addStepC

end DomainTheory.DataTypesAsLattices
