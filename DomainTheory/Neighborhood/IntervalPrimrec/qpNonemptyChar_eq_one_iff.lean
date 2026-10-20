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
import DomainTheory.Neighborhood.IntervalPrimrec.qpNonemptyBop_eq_one_iff


namespace DomainTheory.Neighborhood

open Domain.Recursive








































theorem qpNonemptyChar_eq_one_iff (c : ℕ) :
    qpNonemptyChar c = 1 ↔ ∃ e ∈ decodeList c, (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyChar
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [unpair_pair_fst, qpNonemptyBop_eq_one_iff]

end DomainTheory.Neighborhood
