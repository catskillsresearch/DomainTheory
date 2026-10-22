module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Rcomb_app_zero (x : Pomega) :
    funOf (funOf Rcomb x) (ofNat 0) = ofNat 0 := by
  rw [Rcomb_app, seq2_app_zero]

end DomainTheory.DataTypesAsLattices
