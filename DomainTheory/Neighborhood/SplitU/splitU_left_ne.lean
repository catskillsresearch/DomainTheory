/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.UX_splitURight
import DomainTheory.Neighborhood.SplitU.splitU_disjoint


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

















/-- **Theorem 8.8(b) Part 4, properness (left)**: `splitULeft n` is a *proper* subset of `Xₙ`. -/
theorem splitU_left_ne (n : ℕ) : UX (splitULeft n) ≠ UX n := by
  intro hEq
  have hZsub : UX (splitURight n) ⊆ UX (splitULeft n) := by
    rw [hEq, UX_splitURight]; exact Set.inter_subset_left
  have hZempty : UX (splitURight n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter hZsub subset_rfl
  exact (U_mem_UX (splitURight n)).2.1.ne_empty (Set.subset_empty_iff.mp hZempty)

end DomainTheory.Neighborhood
