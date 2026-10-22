/-ai
The functional vaalF fixes its least fixed point vaalC.

This is the fixed-point identity in Theorem 1.4, applied to Scott continuity of vaalF.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem vaalC_fixedPoint : vaalF vaalC = vaalC :=
  (theorem_1_4 vaalF_isScottContinuous).1

end DomainTheory.DataTypesAsLattices
