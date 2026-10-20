/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.UComputablePresentation.Basic
import DomainTheory.Neighborhood.UComputablePresentation.decodeQPairList_canonCode_ne_nil


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem































/-- `canonCode c` is never the `0` (empty-list) code. -/
theorem canonCode_ne_zero (c : ℕ) : canonCode c ≠ 0 := by
  intro h
  exact decodeQPairList_canonCode_ne_nil c (by rw [h]; unfold decodeQPairList; rw [decodeList_zero]; rfl)

end DomainTheory.Neighborhood
