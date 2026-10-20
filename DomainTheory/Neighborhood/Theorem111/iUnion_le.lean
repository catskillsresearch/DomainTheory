/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Order.Monotone.Basic
import DomainTheory.Neighborhood.Theorem111.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- `⋃ₙ xₙ` is the **least** upper bound: anything approximated by all `xₙ` approximates the
union from above. -/
theorem iUnion_le (x : ℕ → V.Element) (hmono : Monotone x) (y : V.Element)
    (h : ∀ n, x n ≤ y) : V.iUnion x hmono ≤ y := by
  rintro X ⟨n, hn⟩
  exact h n X hn

end NeighborhoodSystem
end DomainTheory.Neighborhood
