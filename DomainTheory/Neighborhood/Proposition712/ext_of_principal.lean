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

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Choice-free extensionality from agreement on principal inputs (cf. Exercise 6.27). -/
theorem ext_of_principal {β : Type*} {W : NeighborhoodSystem β}
    {f g : ApproximableMap V W}
    (h : ∀ (X : Set α) (hX : V.mem X),
      f.toElementMap (V.principal hX) = g.toElementMap (V.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

end NeighborhoodSystem
end DomainTheory.Neighborhood
