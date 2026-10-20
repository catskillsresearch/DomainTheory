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
public import DomainTheory.Neighborhood.IntervalPrimrec.presentedIntervals_diffAllList

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive




















theorem presentedIntervals_diffLists (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffLists L1 L2) = presentedIntervals L1 \ presentedIntervals L2 := by
  induction L1 with
  | nil => simp [diffLists]
  | cons a l ih =>
    rw [show diffLists (a :: l) L2 = diffAllList a L2 ++ diffLists l L2 from rfl,
      presentedIntervals_append, presentedIntervals_diffAllList, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]

end DomainTheory.Neighborhood
