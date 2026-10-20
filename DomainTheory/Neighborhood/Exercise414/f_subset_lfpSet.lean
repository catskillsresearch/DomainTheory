/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic
import DomainTheory.Neighborhood.Exercise414.Basic
import DomainTheory.Neighborhood.Exercise414.lfpSet_subset


namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}





/-- `f (lfpSet f) ⊆ lfpSet f`: it is a pre-fixed point. -/
theorem f_subset_lfpSet (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) ⊆ lfpSet f := by
  intro a ha x hx
  exact hx (hf (lfpSet_subset f hx) ha)

end DomainTheory.Neighborhood.Exercise414
