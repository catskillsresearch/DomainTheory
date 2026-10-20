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
import DomainTheory.Neighborhood.Exercise722.streamArrow_le_mul_self
import DomainTheory.Neighborhood.Exercise722.streamArrow_mul_self_le


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **Exercise 7.22l (Scott's first equation, unconditional).** `σ⃗·σ⃗ = σ⃗`, for the genuine
least-fixed-point `σ⃗`, with no side-condition. -/
theorem streamArrow_mul_self (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) = streamArrow σ :=
  le_antisymm (streamArrow_mul_self_le σ) (streamArrow_le_mul_self σ)

end Exercise722
end DomainTheory.Neighborhood
