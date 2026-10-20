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
import DomainTheory.Neighborhood.IntervalPrimrec.primrec_diffCode
import DomainTheory.Neighborhood.IntervalPrimrec.recDecidable_presentedIntervals_nonempty
import DomainTheory.Neighborhood.IntervalPrimrec.presentedIntervals_decodeQPairList_subset_iff


namespace DomainTheory.Neighborhood

open Domain.Recursive








































/-- **Subset between `presentedIntervals`-coded sets is recursively decidable.** -/
theorem recDecidable₂_presentedIntervals_subset :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp primrec_diffCode).not
  exact presentedIntervals_decodeQPairList_subset_iff t.unpair.1 t.unpair.2

end DomainTheory.Neighborhood
