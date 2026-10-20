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

/-- `a ≤ idMap E` unwound at the element level: `a(x) ≤ x` for every `x`. -/
theorem toElementMap_le_self_of_le_idMap {a : ApproximableMap E E} (ha : a ≤ idMap E)
    (x : E.Element) : a.toElementMap x ≤ x := by
  have h := (le_iff_toElementMap_le.mp ha) x
  rwa [toElementMap_idMap] at h

end DomainTheory.Neighborhood
