/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices
































/-- Isolated points of a closure are its values on finite sets, and
conversely every `a(e n)` is a typed point. -/
theorem theorem_5_1_isolated {a : Pomega} (_ha : IsClosure a) {x : Pomega}
    (hx : typed x a) :
    IsIsolated x → ∃ n, x = funOf a (e n) := by
  intro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn] at hx ⊢
  exact hx

end DomainTheory.DataTypesAsLattices
