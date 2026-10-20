/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)










































































/-- **Membership in a function-space step set, as inclusion of `Xenum`s.** `∀ f ∈ W, f.rel X Y` iff
`W ⊆ step X Y` (`mem_step`); specialised to `W = Xenum … c` and the singleton step neighbourhood
(`Xenum_singleton`), this becomes the *decidable* function-space inclusion `incl_computable`. -/
theorem forall_rel_iff_subset_step {W : Set (ApproximableMap PN PN)} {n m₀ : ℕ} :
    (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ↔ W ⊆ step (nbhd n) (nbhd m₀) := by
  constructor
  · intro h f hf; exact mem_step.mpr (h f hf)
  · intro h f hf; exact mem_step.mp (h hf)

end DomainTheory.Neighborhood.Exercise723
