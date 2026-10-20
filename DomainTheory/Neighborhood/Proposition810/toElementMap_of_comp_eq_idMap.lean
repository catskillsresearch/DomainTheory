/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Proposition810.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- If `j ∘ i = I_D`, then `j(i(v)) = v` for every `v ∈ |D|`. -/
theorem toElementMap_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) (v : D.Element) : j.toElementMap (i.toElementMap v) = v := by
  rw [← toElementMap_comp, hji, toElementMap_idMap]

end DomainTheory.Neighborhood
