/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise817.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}











/-- **`𝒰` is universal** (restating Theorem 8.8(a) in `⊴`-shape). -/
theorem U_isUniversal : IsUniversal.{u} U := by
  intro α D _
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

end DomainTheory.Neighborhood
