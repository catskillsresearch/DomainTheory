/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition610
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Proposition612.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}





/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`. -/
theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

end Subsystem
end DomainTheory.Neighborhood
