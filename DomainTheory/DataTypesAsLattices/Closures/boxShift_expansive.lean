/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_expansive {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    x ⊆ funOf (boxShift a) x := by
  rw [boxShift_app]
  intro k hk
  cases k with
  | zero => exact Or.inl rfl
  | succ k =>
    refine Or.inr ⟨k, ?_, rfl⟩
    have hx : predSet x ⊆ funOf a (predSet x) := by
      have := funOf_monotone_left ha.1 (predSet x)
      rwa [Icomb_app] at this
    exact hx hk

end DomainTheory.DataTypesAsLattices
