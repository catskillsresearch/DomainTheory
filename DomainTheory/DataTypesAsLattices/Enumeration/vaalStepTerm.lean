module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Enumeration.gClosed
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def vaalStepTerm : Term :=
  .lam 0 (.lam 1
    (.cond (.app (.var 1) .zero) gClosed
      (.app
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))))

namespace vaalStepTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp :
    _root_.DomainTheory.DataTypesAsLattices.interp vaalStepTerm (fun _ => botElem) = graph vaalF := by
  unfold vaalStepTerm vaalF

  apply congrArg graph
  funext v
  apply congrArg graph
  funext x
  show condSet (_root_.DomainTheory.DataTypesAsLattices.interp (.app (.var 1) .zero)
        (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (_root_.DomainTheory.DataTypesAsLattices.interp gClosed (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (_root_.DomainTheory.DataTypesAsLattices.interp
        (.app
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))
        (envSet (envSet (fun _ => botElem) 0 v) 1 x)) =
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))
  rw [gClosed.interp]
  simp [_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update, succSet.ofNat]

end vaalStepTerm

end DomainTheory.DataTypesAsLattices
