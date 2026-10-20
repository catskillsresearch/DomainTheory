/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.Neighborhood.Exercise414.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}



/-- Every post-fixed point `x ⊆ f(x)` is contained in `gfpSet f`. -/
theorem subset_gfpSet (f : Set A → Set A) {x : Set A} (hx : x ⊆ f x) : x ⊆ gfpSet f :=
  fun _ ha => ⟨x, hx, ha⟩

end DomainTheory.Neighborhood.Exercise414
