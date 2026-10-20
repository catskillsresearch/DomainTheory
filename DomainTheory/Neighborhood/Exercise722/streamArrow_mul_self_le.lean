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
import DomainTheory.Neighborhood.Exercise722.prependMap_iterElem_mul_streamArrow_le


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`σ⃗·σ⃗ ≤ σ⃗`**: `σ⃗`'s membership witnesses come from *some* finite approximant `fⁿ(⊥)`
(`mem_fixElement`/`mem_iterElem`), and every approximant satisfies the per-`n` bound above. -/
theorem streamArrow_mul_self_le (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) ≤ streamArrow σ := by
  rintro Z ⟨hInSZ, X, hX, Y, hY, hsub⟩
  obtain ⟨n, hn⟩ := (mem_fixElement (prependMap σ)).mp hX
  have hXn : ((prependMap σ).iterElem n).mem X := (mem_iterElem (prependMap σ) n).mpr hn
  exact prependMap_iterElem_mul_streamArrow_le σ n Z ⟨hInSZ, X, hXn, Y, hY, hsub⟩

end Exercise722
end DomainTheory.Neighborhood
