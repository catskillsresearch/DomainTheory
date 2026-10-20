/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise407
import DomainTheory.Neighborhood.Exercise410
import DomainTheory.Neighborhood.Exercise411.Basic
import DomainTheory.Neighborhood.Exercise411.inclMap_toElementMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- The inclusion intertwines `f'` with `f`: `ι ∘ f' = f ∘ ι` (from `relMap_toElementMap_embed`). -/
theorem inclMap_intertwine (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a)
    (g : (relSystem a).Element) :
    (inclMap a).toElementMap ((relMap f ha).toElementMap g) =
      f.toElementMap ((inclMap a).toElementMap g) := by
  rw [inclMap_toElementMap, inclMap_toElementMap, relMap_toElementMap_embed]

end ApproximableMap
end DomainTheory.Neighborhood
