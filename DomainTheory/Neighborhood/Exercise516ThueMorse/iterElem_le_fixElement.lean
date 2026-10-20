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
















/-- Each approximant is below the least fixed point. -/
theorem iterElem_le_fixElement {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
    (n : ℕ) : f.iterElem n ≤ f.fixElement := by
  rw [f.fixElement_eq_iSupDirected]
  intro Z hZ
  rw [mem_iSupDirected]
  exact ⟨n, hZ⟩

end DomainTheory.Neighborhood.Exercise516
