/-ai
Applying the positive bar branch of u and x to the numeral 1 yields u.

Rewrite by the definition and by equation (2.22), which turns sequence cons into a conditional on the argument. The predecessor of the numeral 1 is the numeral 0, by extensionality and simplification of predecessor and numeral. The successor case of the conditional (2.7) and sequencing at the numeral 0 then return u.
ai-/
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


theorem barPos_one (u x : Pomega) :
    funOf (barPos u x) (ofNat 1) = u := by
  rw [barPos, eq_2_22]
  have hpred : predSet (ofNat 1) = ofNat 0 := by
    ext k; simp [predSet, ofNat]
  rw [hpred, eq_2_7_succ, seq2_app_zero]

end DomainTheory.DataTypesAsLattices
