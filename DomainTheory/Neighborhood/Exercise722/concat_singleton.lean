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


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap








/-- `{a}{b} = {a ++ b}`: concatenation of singletons is the singleton of the concatenation. -/
theorem concat_singleton (a b : List Bool) : concat {a} {b} = {a ++ b} := by
  ext w
  simp only [mem_concat, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a', rfl, b', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, b, rfl, rfl⟩

end Exercise722
end DomainTheory.Neighborhood
