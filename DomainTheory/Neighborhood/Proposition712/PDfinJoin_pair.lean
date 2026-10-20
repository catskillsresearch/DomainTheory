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








/-- **Proposition 7.12 — binary intersection law (elementwise).** `{x, y} = {x} ∩ {y}`. -/
theorem PDfinJoin_pair (x y : V.Element) :
    V.PDfinJoin 2 ![x, y] = V.PDsingletonMeet (V.PDsingleton x) (V.PDsingleton y) := by
  apply PDext
  intro W
  simp only [PDsingletonMeet_mem, PDmem_singleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨⟨X 0, hX 0, hPD, hsub 0⟩, ⟨X 1, hX 1, hPD, hsub 1⟩⟩
  · rintro ⟨⟨X0, hx, hPD, hsub0⟩, ⟨X1, hy, _, hsub1⟩⟩
    refine ⟨![X0, X1], ?_, hPD, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

end NeighborhoodSystem
end DomainTheory.Neighborhood
