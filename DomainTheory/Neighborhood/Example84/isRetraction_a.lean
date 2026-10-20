/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Example84.Basic
import DomainTheory.Neighborhood.Example84.a_bot
import DomainTheory.Neighborhood.Example84.a_of_ne_bot


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂











variable {α : Type*} {D : NeighborhoodSystem α}











variable (u : D.Element) (hu : u ≠ D.bot)



/-- **Example 8.4(a) (Scott 1981, PRG-19).** `a` is a retraction. -/
theorem isRetraction_a (hu : u ≠ D.bot) : IsRetraction (a u) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  by_cases hx : x = D.bot
  · subst hx; rw [a_bot, a_bot]
  · rw [a_of_ne_bot u hx, a_of_ne_bot u hu]

end DomainTheory.Neighborhood
