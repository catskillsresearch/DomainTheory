/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Example84.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂











variable {α : Type*} {D : NeighborhoodSystem α}











variable (u : D.Element) (hu : u ≠ D.bot)



theorem a_bot : (a u).toElementMap D.bot = D.bot := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_bot]
  exact ⟨fun ⟨_, h⟩ => h.resolve_right (fun h' => h'.1 rfl) |>.symm ▸ rfl,
    fun h => ⟨h ▸ D.master_mem, Or.inl h⟩⟩

end DomainTheory.Neighborhood
