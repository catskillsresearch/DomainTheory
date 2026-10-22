module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem barPos_two (u x : Pomega) :
    funOf (barPos u x) (ofNat 2) = funOf x (ofNat 1) := by
  rw [barPos, eq_2_22]
  have hpred : predSet (ofNat 2) = ofNat 1 := by
    ext k; simp [predSet, ofNat]
  rw [hpred, eq_2_7_succ, seq2_app_one]

end DomainTheory.DataTypesAsLattices
