/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem88m
import DomainTheory.Neighborhood.Exercise816.Basic
import DomainTheory.Neighborhood.Exercise816.isFinitaryProjection_le_iff_fixedNbhd_subsystem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Exercise 8.16 (Scott 1981, PRG-19), in full.**

Part 1: for finitary projections `a, b : E → E`, `a ≤ b ↔ D_a ◁ D_b` (fills the gap at the end of
Theorem 8.6's proof).

Part 2: if `a : E → E` is computable relative to a `ComputablePresentation P` of `E` — i.e. `E` is
effectively given (via `P`) and `a` is computable (relative to `P`) — then `D_a` is effectively
given (finishes off Theorem 8.8's proof). This is `Theorem88m.lean`'s `fixedNbhd_isEffectivelyGiven`,
cited here under the exercise's name. -/
theorem exercise_8_16 :
    (∀ {a b : ApproximableMap E E}, IsFinitaryProjection a → IsFinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        IsComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  ⟨fun ha hb => isFinitaryProjection_le_iff_fixedNbhd_subsystem ha hb,
    fun hcomp => fixedNbhd_isEffectivelyGiven hcomp⟩

end DomainTheory.Neighborhood
