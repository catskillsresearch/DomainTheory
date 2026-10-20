/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalF_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalStepTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




























































theorem vaalC_combinatory : IsCombinatory vaalC := by
  have hY : funOf Ycomb (interp vaalStepTerm (fun _ => botElem)) = vaalC := by
    rw [vaalStepTerm_interp, theorem_2_5 vaalF_isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed vaalStepTerm)

end DomainTheory.DataTypesAsLattices
