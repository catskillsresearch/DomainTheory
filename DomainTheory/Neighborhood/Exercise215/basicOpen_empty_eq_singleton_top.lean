/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Exercise215.Basic


namespace DomainTheory.Neighborhood.Exercise215

open DomainTheory.Neighborhood NeighborhoodSystem
















/-- The open point `{⊤}` is the basic open `[∅]`. -/
theorem basicOpen_empty_eq_singleton_top : O.basicOpen ∅ = {topElt} := by
  ext x
  rw [mem_basicOpen, mem_empty_iff_eq_top]
  exact Set.mem_singleton_iff.symm

end DomainTheory.Neighborhood.Exercise215
