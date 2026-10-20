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
import DomainTheory.Neighborhood.IntervalPrimrec.primrec_qpNonemptyChar
import DomainTheory.Neighborhood.IntervalPrimrec.qpNonemptyChar_le_one
import DomainTheory.Neighborhood.IntervalPrimrec.presentedIntervals_decodeQPairList_nonempty_iff


namespace DomainTheory.Neighborhood

open Domain.Recursive








































/-- **Non-emptiness of the set presented by a QPair-list code is recursively decidable.** -/
theorem recDecidable_presentedIntervals_nonempty :
    RecDecidable (fun c => (presentedIntervals (decodeQPairList c)).Nonempty) :=
  RecDecidable.of_zero_one_char primrec_qpNonemptyChar
    (fun c => by have := qpNonemptyChar_le_one c; omega)
    presentedIntervals_decodeQPairList_nonempty_iff

end DomainTheory.Neighborhood
