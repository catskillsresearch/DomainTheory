/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Exercise812c.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem


/-- **`U` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty): `IntervalPrimrec.lean`'s `diffLists`/`presentedIntervals_diffLists`, built unconditionally
from `Ico_diff_Ico`, already witnesses presentability of the raw difference; only non-emptiness can
fail. -/
theorem U_diff_mem {X Y : Set ℚ} (hX : U.mem X) (hY : U.mem Y) : X \ Y = ∅ ∨ U.mem (X \ Y) := by
  obtain ⟨⟨L1, rfl⟩, -, hXsub⟩ := hX
  obtain ⟨⟨L2, rfl⟩, -, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (presentedIntervals L1 \ presentedIntervals L2) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨diffLists L1 L2, (presentedIntervals_diffLists L1 L2).symm⟩, h,
      Set.sdiff_subset.trans hXsub⟩

end DomainTheory.Neighborhood
