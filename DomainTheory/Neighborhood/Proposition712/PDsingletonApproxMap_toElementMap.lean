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
import DomainTheory.Neighborhood.Proposition712.PDext


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)





/-- **Proposition 7.12 — action of `λ x. {x}`.** `(λ x. {x})(x) = {x}` for every `x ∈ |𝒟|`. -/
theorem PDsingletonApproxMap_toElementMap (x : V.Element) :
    (PDsingletonApproxMap (V := V)).toElementMap x = V.PDsingleton x := by
  apply PDext
  intro W
  rw [ApproximableMap.mem_toElementMap, PDmem_singleton]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hxX)] at hrel
    rw [PDmem_singleton] at hrel
    obtain ⟨Y, ⟨hYmem, hXY⟩, hPD, hsub⟩ := hrel
    exact ⟨Y, x.up_mem hxX hYmem hXY, hPD, hsub⟩
  · intro hW
    obtain ⟨Y, hy, hPD, hsub⟩ := hW
    refine ⟨Y, hy, ?_⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hy), PDmem_singleton]
    exact ⟨Y, ⟨x.sub hy, subset_rfl⟩, hPD, hsub⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
