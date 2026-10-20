/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example24
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise218.Basic
import DomainTheory.Neighborhood.Exercise218.toElementMap_kMap_cone


namespace DomainTheory.Neighborhood.Exercise218

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap















/-- **Exercise 2.18 — `k` is not one-one.** `↑(0Σ*)` and `↑(1Σ*)` are distinct finite elements that
`k` collapses to `⊥` (a length-1 prefix is an incomplete pair, so its bit is dropped). -/
theorem kMap_not_injective : ¬ Function.Injective kMap.toElementMap := by
  intro hinj
  have h1 : kMap.toElementMap (B.principal (memB_cone [false]))
      = kMap.toElementMap (B.principal (memB_cone [true])) := by
    rw [toElementMap_kMap_cone, toElementMap_kMap_cone]; rfl
  have h2 := hinj h1
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) h2)
  simp at hcone

end DomainTheory.Neighborhood.Exercise218
