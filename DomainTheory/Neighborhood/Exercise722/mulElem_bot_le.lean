/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert
import DomainTheory.Neighborhood.Exercise722.Basic
import DomainTheory.Neighborhood.Exercise722.Ssys_master


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`⊥` is a left-annihilator up to `≤`**: `⊥·y ≤ y`. (`⊥`'s only neighbourhood is `Δ = Σ`, and
`Y ⊆ Σ·Y` via the empty-word split, so any witness collapses onto `y` itself.) -/
theorem mulElem_bot_le (y : Ssys.Element) : mulElem Ssys.bot y ≤ y := by
  rintro Z ⟨hInS, X, hX, Y, hY, hsub⟩
  rw [NeighborhoodSystem.mem_bot, Ssys_master] at hX
  subst hX
  refine y.up_mem hY hInS fun w hw => hsub ?_
  simpa using append_mem_concat (Set.mem_univ ([] : List Bool)) hw

end Exercise722
end DomainTheory.Neighborhood
