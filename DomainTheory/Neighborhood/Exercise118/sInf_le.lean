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








/-- `sInf F ⊑ x` for every `x ∈ F`. -/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

end NeighborhoodSystem
end DomainTheory.Neighborhood
