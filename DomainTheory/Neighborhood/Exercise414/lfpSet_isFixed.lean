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
import DomainTheory.Neighborhood.Exercise414.f_subset_lfpSet


namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}





/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is a fixed point: `f(b) = b`. -/
theorem lfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) = lfpSet f := by
  have hsub : f (lfpSet f) ⊆ lfpSet f := f_subset_lfpSet f hf
  have hsup : lfpSet f ⊆ f (lfpSet f) := lfpSet_subset f (hf hsub)
  exact Set.Subset.antisymm hsub hsup

end DomainTheory.Neighborhood.Exercise414
