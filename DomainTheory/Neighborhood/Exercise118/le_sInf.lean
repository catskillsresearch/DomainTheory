/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise118.Basic


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood



namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- `sInf F` is the **greatest** lower bound of `F`. -/
theorem le_sInf (F : Set V.Element) (hF : F.Nonempty) (y : V.Element) (h : ∀ x ∈ F, y ≤ x) :
    y ≤ V.sInf F hF :=
  fun _ hX x hx => h x hx _ hX

end NeighborhoodSystem
end DomainTheory.Neighborhood
