/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import Mathlib.Data.Set.Image
import DomainTheory.Neighborhood.ApproximableExercises.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem mem_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α} :
    (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z := by
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hsZ⟩; exact ⟨i, hsZ⟩
  · rintro ⟨i, hi⟩; exact ⟨a i, ⟨i, rfl⟩, hi⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
