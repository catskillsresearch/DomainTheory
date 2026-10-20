/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic
import DomainTheory.Neighborhood.Exercise414.Basic
import DomainTheory.Neighborhood.Exercise414.subset_gfpSet
import DomainTheory.Neighborhood.Exercise414.gfpSet_subset_f


namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}



/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is a fixed point: `f(g) = g`. -/
theorem gfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (gfpSet f) = gfpSet f := by
  have hsub : gfpSet f ⊆ f (gfpSet f) := gfpSet_subset_f f hf
  have hsup : f (gfpSet f) ⊆ gfpSet f := subset_gfpSet f (hf hsub)
  exact Set.Subset.antisymm hsup hsub

end DomainTheory.Neighborhood.Exercise414
