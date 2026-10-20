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


namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}



/-- `gfpSet f ⊆ f (gfpSet f)`: it is a post-fixed point. -/
theorem gfpSet_subset_f (f : Set A → Set A) (hf : Monotone f) :
    gfpSet f ⊆ f (gfpSet f) := by
  rintro a ⟨x, hx, hax⟩
  exact hf (subset_gfpSet f hx) (hx hax)

end DomainTheory.Neighborhood.Exercise414
