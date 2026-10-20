/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.UX_splitULeft
import DomainTheory.Neighborhood.SplitU.UX_splitURight


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

















/-- **Theorem 8.8(b) Part 4, disjointness**: `splitULeft`/`splitURight` cover disjoint pieces. -/
theorem splitU_disjoint (n : ℕ) : UX (splitULeft n) ∩ UX (splitURight n) = ∅ := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

end DomainTheory.Neighborhood
