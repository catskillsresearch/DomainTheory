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




/-- `⋂ₙ xₙ` is the **greatest** lower bound: anything approximating all `xₙ` approximates `⋂ₙ xₙ`. -/
theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

end NeighborhoodSystem
end DomainTheory.Neighborhood
