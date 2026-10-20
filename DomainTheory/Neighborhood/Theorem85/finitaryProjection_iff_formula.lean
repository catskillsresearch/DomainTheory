/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem85.Basic
import DomainTheory.Neighborhood.Theorem85.isFinitaryProjection_of_formula
import DomainTheory.Neighborhood.Theorem85.formula_of_isFinitaryProjection


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}







/-- **Theorem 8.5 (Scott 1981, PRG-19), in full.** `a : E → E` is a finitary projection iff it
satisfies the step-closure formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`. -/
theorem finitaryProjection_iff_formula (a : ApproximableMap E E) :
    IsFinitaryProjection a ↔ ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X :=
  ⟨fun h => formula_of_isFinitaryProjection h, fun hii => isFinitaryProjection_of_formula a hii⟩

end DomainTheory.Neighborhood
