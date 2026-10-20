module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.gClosed_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




























































theorem vaalStepTerm_interp :
    interp vaalStepTerm (fun _ => botElem) = graph vaalF := by
  unfold vaalStepTerm vaalF
  -- `interp (.lam i t)` is definitionally a graph; keep `gClosed` packed.
  apply congrArg graph
  funext v
  apply congrArg graph
  funext x
  show condSet (interp (.app (.var 1) .zero)
        (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (interp gClosed (envSet (envSet (fun _ => botElem) 0 v) 1 x))
      (interp
        (.app
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
          (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))
        (envSet (envSet (fun _ => botElem) 0 v) 1 x)) =
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))
  rw [gClosed_interp]
  simp [interp, envSet, Function.update, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
