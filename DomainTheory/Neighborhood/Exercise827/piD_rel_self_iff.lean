/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap









































/-- **Exercise 8.27(b)(2), specialized to self-relation** (the shape Theorem 8.5's formula (ii)
actually tests, `a.rel X X`): combines (a) and (b) into the single membership-test formula that
Exercise 8.27(b)(3) will chain through `subU`'s and each `D'_s`'s own formula (ii). -/
theorem piD_rel_self_iff (d : ApproximableMap U U) {X : Set (ApproximableMap U U)} :
    (piD d).rel X X ↔ ∃ hX : (funSpace U U).mem X, gSection (piDUncurried d) hX ∈ X := by
  rw [piD_rel_iff]
  exact ⟨fun ⟨hX, _, hmem⟩ => ⟨hX, hmem⟩, fun ⟨hX, hmem⟩ => ⟨hX, hX, hmem⟩⟩

end DomainTheory.Neighborhood
