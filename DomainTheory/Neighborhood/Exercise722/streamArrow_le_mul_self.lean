/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.Neighborhood.Exercise722.Basic
public import DomainTheory.Neighborhood.Exercise722.prependMap_toElementMap
public import DomainTheory.Neighborhood.Exercise722.streamArrow_eq

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`σ⃗ ≤ σ⃗·σ⃗`**: `σ⃗·σ⃗` is itself a fixed point of `x ↦ σ·x` (by associativity and `σ⃗ = σ·σ⃗`),
and `σ⃗` is the *least* such fixed point (`fixElement_le_of_toElementMap_le`). -/
theorem streamArrow_le_mul_self (σ : List Bool) :
    streamArrow σ ≤ mulElem (streamArrow σ) (streamArrow σ) := by
  apply fixElement_le_of_toElementMap_le
  have heq : (prependMap σ).toElementMap (mulElem (streamArrow σ) (streamArrow σ)) =
      mulElem (streamArrow σ) (streamArrow σ) := by
    rw [prependMap_toElementMap, ← mulElem_assoc, streamArrow_eq]
  exact le_of_eq heq

end Exercise722
end DomainTheory.Neighborhood
