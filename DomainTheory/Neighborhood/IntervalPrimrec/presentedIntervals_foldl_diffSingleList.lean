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


namespace DomainTheory.Neighborhood

open Domain.Recursive



















theorem presentedIntervals_foldl_diffSingleList (L2 : List (ℚ × ℚ)) :
    ∀ acc : List (ℚ × ℚ),
      presentedIntervals (L2.foldl diffSingleList acc) = presentedIntervals acc \ presentedIntervals L2 := by
  induction L2 with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih (diffSingleList acc a), presentedIntervals_diffSingleList,
      presentedIntervals_cons, Set.sdiff_sdiff]

end DomainTheory.Neighborhood
