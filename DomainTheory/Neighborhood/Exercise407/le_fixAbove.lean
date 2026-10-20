/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise407.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap







/-- `a ⊑ fixAbove f ha`: the constructed fixed point lies above `a` (it is the `n = 0` term). -/
theorem le_fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    a ≤ f.fixAbove ha := by
  have := NeighborhoodSystem.le_iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩) 0
  rwa [iterFrom_zero] at this

end ApproximableMap
end DomainTheory.Neighborhood
