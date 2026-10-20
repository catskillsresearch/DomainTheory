/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.UX_splitULeft
import DomainTheory.Neighborhood.SplitU.splitU_disjoint


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

















/-- **Theorem 8.8(b) Part 4, properness (right)**: `splitURight n` is a *proper* subset of `Xₙ`. -/
theorem splitU_right_ne (n : ℕ) : UX (splitURight n) ≠ UX n := by
  intro hEq
  have hYsub : UX (splitULeft n) ⊆ UX (splitURight n) := by
    rw [hEq, UX_splitULeft]; exact Set.inter_subset_left
  have hYempty : UX (splitULeft n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter subset_rfl hYsub
  exact (U_mem_UX (splitULeft n)).2.1.ne_empty (Set.subset_empty_iff.mp hYempty)

end DomainTheory.Neighborhood
