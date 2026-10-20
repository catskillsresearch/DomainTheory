/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Exercise120
import Mathlib.Tactic
import DomainTheory.Neighborhood.Definition79.Basic
import DomainTheory.Neighborhood.Definition79.mem_PDunion


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- **Definition 7.9 — the empty union.** "The finite unions in `ℙ𝒟` can be empty (i.e. if
`n = 0`)." The empty neighbourhood `∅` is a neighbourhood of `ℙ𝒟` (witnessed by `L = []`). -/
theorem PDmem_empty : V.PDmem ∅ := by
  refine ⟨[], ?_, ?_⟩
  · intro X hX; cases hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro h; exact absurd h (Set.notMem_empty z)
    · rintro ⟨X, hX, _⟩; cases hX

end NeighborhoodSystem
end DomainTheory.Neighborhood
