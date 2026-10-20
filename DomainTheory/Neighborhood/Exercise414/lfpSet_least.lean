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





/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is the *least* fixed point: any fixed
point `y = f(y)` satisfies `b ⊆ y`. -/
theorem lfpSet_least (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    lfpSet f ⊆ y := lfpSet_subset f (le_of_eq hy)

end DomainTheory.Neighborhood.Exercise414
