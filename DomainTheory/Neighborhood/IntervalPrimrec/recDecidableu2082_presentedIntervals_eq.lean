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
import DomainTheory.Neighborhood.IntervalPrimrec.recDecidableu2082_presentedIntervals_subset


namespace DomainTheory.Neighborhood

open Domain.Recursive








































/-- **Equality between `presentedIntervals`-coded sets is recursively decidable**, from
`recDecidable₂_presentedIntervals_subset` in both directions (`Set.Subset.antisymm_iff`). -/
theorem recDecidable₂_presentedIntervals_eq :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) = presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable₂_presentedIntervals_subset.and recDecidable₂_presentedIntervals_subset.swap)
  exact Set.Subset.antisymm_iff

end DomainTheory.Neighborhood
