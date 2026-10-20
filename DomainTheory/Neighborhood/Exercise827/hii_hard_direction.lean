/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.exists_X_of_mem_stepFun


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27(b)(3), the `⟹` half, closed for any `d` at all.** Destructure the general
`Y : Set (ApproximableMap U U)` via `funSpace_mem_iff` into `Y = stepFun L`, then apply
`exists_X_of_mem_stepFun`. -/
theorem hii_hard_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    (hmem : piDApply d (toApproxMap x) ∈ Y) :
    ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hYE
  exact exists_X_of_mem_stepFun d x L hmem

end DomainTheory.Neighborhood
