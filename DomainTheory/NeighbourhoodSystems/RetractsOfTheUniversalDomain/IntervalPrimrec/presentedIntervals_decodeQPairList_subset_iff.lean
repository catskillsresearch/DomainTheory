/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition87
public import DomainTheory.Neighborhood.RationalPrimrec
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive








































/-- **Subset between `presentedIntervals`-coded sets reduces to non-emptiness of `diffCode`.** -/
theorem presentedIntervals_decodeQPairList_subset_iff (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2) ↔
      ¬ (presentedIntervals (decodeQPairList (diffCode c1 c2))).Nonempty := by
  rw [presentedIntervals_decodeQPairList_diffCode, Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

end DomainTheory.Neighborhood
