/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_typed_bot
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_typed_top
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_typed_inl
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_typed_inr


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Range of the paper sum. -/
theorem boxPlus_typed_iff {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed u (boxPlus a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = squarePair x botElem ∧ typed x (boxShift a)) ∨
          (∃ y, u = squarePair botElem y ∧ typed y (boxShift b)) := by
  constructor
  · intro hu
    have hu' : u = funOf (boxPlus a b) u := hu
    by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
    · exact Or.inl (hu'.trans (boxPlus_app_empty hx hy))
    · refine Or.inr (Or.inr (Or.inr ⟨funOf (boxShift b) (squareSnd u), ?_, ?_⟩))
      · exact hu'.trans (boxPlus_app_right hx hy)
      · exact (retract_app (boxShift_isRetract hb) (squareSnd u)).symm
    · refine Or.inr (Or.inr (Or.inl ⟨funOf (boxShift a) (squareFst u), ?_, ?_⟩))
      · exact hu'.trans (boxPlus_app_left hx hy)
      · exact (retract_app (boxShift_isRetract ha) (squareFst u)).symm
    · exact Or.inr (Or.inl (hu'.trans (boxPlus_app_mixed hx hy)))
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact boxPlus_typed_bot a b
    · rw [hu]; exact boxPlus_typed_top a b
    · rw [hx]; exact boxPlus_typed_inl hxt
    · rw [hy]; exact boxPlus_typed_inr hyt

end DomainTheory.DataTypesAsLattices
