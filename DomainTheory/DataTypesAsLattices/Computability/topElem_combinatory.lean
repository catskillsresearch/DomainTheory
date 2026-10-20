/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem topElem_combinatory : IsCombinatory topElem := by
  have h : funOf Ycomb (interp topRecTerm (fun _ => botElem)) = topElem := by
    rw [topRecTerm_interp, theorem_2_5 topRec_isScottContinuous, eq_2_16]
  exact h ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed topRecTerm)

end DomainTheory.DataTypesAsLattices
