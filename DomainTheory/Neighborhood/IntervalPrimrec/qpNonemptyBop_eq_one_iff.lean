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







































theorem qpNonemptyBop_eq_one_iff (e : ℕ) :
    qpNonemptyBop e = 1 ↔ (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyBop decodeRatPair; exact ratLtCode_eq_one_iff e.unpair.1 e.unpair.2

end DomainTheory.Neighborhood
