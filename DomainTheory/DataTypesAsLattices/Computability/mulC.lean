module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
public import DomainTheory.DataTypesAsLattices.Computability.SK_comp
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_mul

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def mulC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb
          (funOf Kcomb
            (funOf (interp primRecStepTerm (fun _ => botElem)) (ofNat 0))))
        (funOf (funOf Scomb (funOf Kcomb Kcomb)) addC)))

namespace mulC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (x : Pomega) :
    mulC ⬝ x = primRecComb (ofNat 0) (Kcomb ⬝ (addC ⬝ x)) := by
  rw [mulC, primRecComb, SK_comp, SK_comp, SK_comp, SK_comp]

theorem combinatory : IsCombinatory mulC :=
  .app (.app .S (.app .K dollarC.combinatory))
    (.app (.app .S (.app .K Ycomb.combinatory))
      (.app (.app .S
          (.app .K (.app (theorem_2_4.closed primRecStepTerm)
            (ofNat.combinatory 0))))
        (.app (.app .S (.app .K .K)) addC.combinatory)))

theorem realizes2 : Realizes2 mulC fun n m => n * m := fun n m => by
  simp [mulC.app, primRecComb.ofNat, primRecVal_mul]

end mulC

end DomainTheory.DataTypesAsLattices
