/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Hinterp_isScottContinuous


namespace DomainTheory.DataTypesAsLattices


































theorem Htyped_app (τ : LambTerm) (t : Pomega) :
    funOf (Htyped τ) t = funOf lambR (Hinterp τ (funOf envR t)) := by
  rw [Htyped, arrowR_app]
  simp only [comp_app]
  apply congrArg (funOf lambR)
  exact beta (Hinterp_isScottContinuous τ) (funOf envR t)

end DomainTheory.DataTypesAsLattices
