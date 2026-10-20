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
import DomainTheory.Neighborhood.Definition87.presentedIntervals_append


namespace DomainTheory.Neighborhood

open NeighborhoodSystem


























/-- **`U` is closed under binary union**, as long as the result is non-empty: if `X` and `Y` are
each either empty or `U`-neighbourhoods, so is `X ∪ Y`. Unlike intersection (Definition 8.7's
`inter_mem`), this needs no consistency witness — `U`'s neighbourhoods are *by definition* finite
unions of intervals, so unioning two presenting lists (`++`) always presents the union. -/
theorem U_union_mem {X Y : Set ℚ} (hX : X = ∅ ∨ U.mem X) (hY : Y = ∅ ∨ U.mem Y) :
    X ∪ Y = ∅ ∨ U.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · rcases hY with rfl | hY
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hY)
  · rcases hY with rfl | hY
    · exact Or.inr (by simpa using hX)
    · obtain ⟨⟨L1, rfl⟩, hXne, hXsub⟩ := hX
      obtain ⟨⟨L2, rfl⟩, hYne, hYsub⟩ := hY
      refine Or.inr ⟨⟨L1 ++ L2, (presentedIntervals_append L1 L2).symm⟩,
        hXne.mono Set.subset_union_left, Set.union_subset hXsub hYsub⟩

end DomainTheory.Neighborhood
