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




























/-- **Scott's third equation.** `σ1⃗ · σ1⃗ = σ1⃗`, where `σ1⃗ := streamArrow (σ ++ [true])` is the
arrow of the *combined* token `σ1` (Scott's notation `σ⃗1⃗` names the infinite repetition of the
word `σ` followed by `1`, not a product of two separate arrows — matching how the file's earlier
`streamElem`-based examples read the same equation). An instance of `streamArrow_mul_self`. -/
theorem streamArrow_mul_self_append_true (σ : List Bool) :
    mulElem (streamArrow (σ ++ [true])) (streamArrow (σ ++ [true])) =
      streamArrow (σ ++ [true]) :=
  streamArrow_mul_self (σ ++ [true])

end Exercise722
end DomainTheory.Neighborhood
