module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.addStepC
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_add

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def addC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb addStepC)))

namespace addC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (x : Pomega) : funOf addC x = primRecComb x addStepC := by
  simp [addC, primRecComb, Scomb.beta3, Kcomb.beta2]

theorem combinatory : IsCombinatory addC :=
  .app (.app .S (.app .K dollarC.combinatory))
    (.app (.app .S (.app .K Ycomb.combinatory))
      (.app (.app .S (theorem_2_4.closed primRecStepTerm))
        (.app .K addStepC.combinatory)))

theorem realizes2 : Realizes2 addC fun n m => n + m := fun n m => by
  simp [addC.app, primRecComb.ofNat, primRecVal_add]

end addC

end DomainTheory.DataTypesAsLattices
