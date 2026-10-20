/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise418.Basic
import DomainTheory.Neighborhood.Exercise418.natElem_injective


namespace DomainTheory.Neighborhood.Exercise418

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** `succ` is injective on the total elements. -/
theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega

end DomainTheory.Neighborhood.Exercise418
