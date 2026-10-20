/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419








/-- A one-step unfolding of the iterated bottom element: `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate]
  exact Function.iterate_succ_apply' f.toElementMap n V.bot

end DomainTheory.Neighborhood.Exercise516
