/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert
import DomainTheory.Neighborhood.Exercise722.Basic
import DomainTheory.Neighborhood.Exercise722.streamArrow_mul_self


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **Scott's second equation.** `σ⃗·σ⃗·σ⃗ = σ⃗`. -/
theorem streamArrow_mul_self_self (σ : List Bool) :
    mulElem (mulElem (streamArrow σ) (streamArrow σ)) (streamArrow σ) = streamArrow σ := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

end Exercise722
end DomainTheory.Neighborhood
