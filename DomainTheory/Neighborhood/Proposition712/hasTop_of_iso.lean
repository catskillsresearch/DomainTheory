/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition711
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Tactic
import DomainTheory.Neighborhood.Proposition712.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-- **`HasTop` transports across domain isomorphisms.** An order-iso `|D| ≃o |D'|` carries the
greatest element of `|D'|` to that of `|D|`. -/
theorem hasTop_of_iso {D : NeighborhoodSystem γ} {D' : NeighborhoodSystem δ}
    (e : D.Element ≃o D'.Element) (h : HasTop D') : HasTop D := by
  obtain ⟨t, ht⟩ := h
  refine ⟨e.symm t, fun x => ?_⟩
  rw [← e.le_iff_le, e.apply_symm_apply]
  exact ht (e x)

end Counterexample712C
end DomainTheory.Neighborhood
