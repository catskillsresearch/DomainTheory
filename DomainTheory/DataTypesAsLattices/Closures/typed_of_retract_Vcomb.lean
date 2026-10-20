/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
import DomainTheory.DataTypesAsLattices.Closures.Vapply_right_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app


namespace DomainTheory.DataTypesAsLattices
































/-- `V` does not change already-closed points of a retract. -/
theorem typed_of_retract_Vcomb {a x : Pomega} (hx : typed x a) :
    typed x (funOf Vcomb a) := by
  rw [typed, Vcomb_app]
  have happ : funOf (graph (fun z => Vapply a z)) x = Vapply a x :=
    beta (Vapply_right_isScottContinuous a) x
  rw [happ]
  apply subset_antisymm
  · exact eq_5_16 a x
  · intro k hk
    exact hk x ⟨subset_rfl, by rw [← hx]⟩


end DomainTheory.DataTypesAsLattices
