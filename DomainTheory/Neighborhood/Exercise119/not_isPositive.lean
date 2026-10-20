/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise119.Basic
import DomainTheory.Neighborhood.Exercise119.a_inter_b
import DomainTheory.Neighborhood.Exercise119.one_not_mem


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood.Exercise119

open DomainTheory.Neighborhood















/-- **Exercise 1.19 — the example is not positive.** `{0,1}` and `{1,2}` are neighbourhoods whose
intersection `{1}` is non-empty but is *not* a neighbourhood, contradicting (ii′). -/
theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)

end DomainTheory.Neighborhood.Exercise119
