/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.RationalPrimrec
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.IntervalPrimrec.Basic
import DomainTheory.Neighborhood.IntervalPrimrec.mem_decodeQPairList_combineCode
import DomainTheory.Neighborhood.IntervalPrimrec.mem_combineIntervals


namespace DomainTheory.Neighborhood

open Domain.Recursive












/-- **`combineCode` realizes `combineIntervals` at the set level.** -/
theorem presentedIntervals_decodeQPairList_combineCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (combineCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∩ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_inter]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_combineCode, mem_combineIntervals]

end DomainTheory.Neighborhood
