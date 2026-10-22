module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF_body_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem vaalF_app (v x : Pomega) :
    funOf (vaalF v) x =
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))) :=
  beta (vaalF_body_isScottContinuous v) x

end DomainTheory.DataTypesAsLattices
