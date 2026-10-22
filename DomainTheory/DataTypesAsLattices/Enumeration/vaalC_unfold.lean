module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF_app
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalC_fixedPoint

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- **Scott 1976, (4.46).** Unfolding of `vaal` at a tree code. -/
theorem vaalC_unfold (x : Pomega) :
    funOf vaalC x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf vaalC (funOf (funOf x (ofNat 1)) (ofNat 1)))) := by
  have h := congrArg (fun v => funOf v x) vaalC_fixedPoint
  simpa [vaalF_app] using h.symm

end DomainTheory.DataTypesAsLattices
