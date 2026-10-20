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
import DomainTheory.Neighborhood.IntervalPrimrec.presentedIntervals_foldl_diffSingleList


namespace DomainTheory.Neighborhood

open Domain.Recursive



















theorem presentedIntervals_diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffAllList p L2) = Set.Ico p.1 p.2 \ presentedIntervals L2 := by
  unfold diffAllList
  rw [presentedIntervals_foldl_diffSingleList, presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]

end DomainTheory.Neighborhood
