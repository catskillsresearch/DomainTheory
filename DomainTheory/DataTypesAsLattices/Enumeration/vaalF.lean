/-ai
Scott 1976, (4.46). The functional vaalF, the companion of val on trees, sends a value v to the graph of the map which on a tree code x returns the McCarthy conditional of the application of x to zero, with zero branch the G combinator and positive branch the application of v at the left child of x to the application of v at the right child.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- **Scott 1976, (4.46).** `vaal` on trees, companion of `val`. -/
def vaalF (v : Pomega) : Pomega :=
  graph (fun x =>
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
