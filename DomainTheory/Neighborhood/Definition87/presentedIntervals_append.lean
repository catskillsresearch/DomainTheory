/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.CompleteLattice.Finset
import DomainTheory.Neighborhood.Definition87.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem


























theorem presentedIntervals_append (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (L1 ++ L2) = presentedIntervals L1 ∪ presentedIntervals L2 := by
  induction L1 with
  | nil => simp
  | cons p L1 ih => simp [List.cons_append, presentedIntervals_cons, ih, Set.union_assoc]

end DomainTheory.Neighborhood
