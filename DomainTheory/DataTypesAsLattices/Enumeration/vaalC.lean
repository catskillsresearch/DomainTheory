module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalStepTerm
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Computability.IsRE

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def vaalC : Pomega := fix vaalF

namespace vaalC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory vaalC := by
  have hY : funOf Ycomb (interp vaalStepTerm (fun _ => botElem)) = vaalC := by
    rw [vaalStepTerm.interp, theorem_2_5 vaalF.isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb.combinatory (theorem_2_4.closed vaalStepTerm)

theorem computable : IsRE vaalC :=
  combinatory_isRE vaalC.combinatory

theorem fixedPoint : vaalF vaalC = vaalC :=
  (theorem_1_4 vaalF.isScottContinuous).1

theorem unfold (x : Pomega) :
    funOf vaalC x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 1)))) := by
  have h := congrArg (fun v => funOf v x) vaalC.fixedPoint
  simpa [vaalF.app] using h.symm

end vaalC

end DomainTheory.DataTypesAsLattices
