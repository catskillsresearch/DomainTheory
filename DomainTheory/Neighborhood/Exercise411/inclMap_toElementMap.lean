/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise407
import DomainTheory.Neighborhood.Exercise410
import DomainTheory.Neighborhood.Exercise411.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- The inclusion's elementwise action is `embed a` (Exercise 4.10). -/
theorem inclMap_toElementMap (a : V.Element) (g : (relSystem a).Element) :
    (inclMap a).toElementMap g = embed a g := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hgX, haX, hVY, hXY⟩
    exact ⟨hVY, X, haX, hgX, hXY⟩
  · rintro ⟨hVY, W, haW, hgW, hWY⟩
    exact ⟨W, hgW, haW, hVY, hWY⟩

end ApproximableMap
end DomainTheory.Neighborhood
