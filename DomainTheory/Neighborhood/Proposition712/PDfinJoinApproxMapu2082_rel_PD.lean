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
import DomainTheory.Neighborhood.Proposition712.PDfinJoin_inter_two


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)













variable (P : ComputablePresentation V)

theorem PDfinJoinApproxMap₂_rel_PD {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (V.PDfinJoin 2 ![V.principal hX, V.principal hY]).mem W := by
  constructor
  · intro ⟨h1, h2⟩
    rw [PDsingletonApproxMap_rel (hX := hX)] at h1
    rw [PDsingletonApproxMap_rel (hX := hY)] at h2
    exact (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).2 ⟨h1, h2⟩
  · intro h
    rcases (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).1 h with ⟨h1, h2⟩
    exact ⟨by rw [PDsingletonApproxMap_rel (hX := hX)]; exact h1,
      by rw [PDsingletonApproxMap_rel (hX := hY)]; exact h2⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
