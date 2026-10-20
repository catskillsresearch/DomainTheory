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

















/-- **Theorem 8.8(b) Part 4, covering**: `splitULeft`/`splitURight` reunite to `Xₙ`. -/
theorem splitU_union (n : ℕ) : UX (splitULeft n) ∪ UX (splitURight n) = UX n := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitMidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

end DomainTheory.Neighborhood
