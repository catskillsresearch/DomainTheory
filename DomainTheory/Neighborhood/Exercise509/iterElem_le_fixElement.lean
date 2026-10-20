/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise407
import DomainTheory.Neighborhood.Exercise509.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `fⁿ(⊥) ⊑ fix(f)`. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement := by
  rw [fixElement_eq_iSupDirected f]
  exact NeighborhoodSystem.le_iSupDirected f.iterElem _ n

end ApproximableMap
end DomainTheory.Neighborhood
