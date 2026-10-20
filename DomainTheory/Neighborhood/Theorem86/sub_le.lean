/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Theorem86.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}



/-- **`sub f ≤ f`, unconditionally (Scott 1981, PRG-19).** "`X ⊆ Y, f Y ⊆ Z` always implies
`X f Z`" — a bare narrow-input/widen-output monotonicity calculation, needing nothing about `f`. -/
theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ

end DomainTheory.Neighborhood
