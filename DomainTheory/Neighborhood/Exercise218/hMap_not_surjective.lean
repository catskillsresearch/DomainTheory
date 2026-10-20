/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example24
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise218.Basic
import DomainTheory.Neighborhood.Exercise218.toElementMap_hMap_cone
import DomainTheory.Neighborhood.Exercise218.toElementMap_kMap_cone
import DomainTheory.Neighborhood.Exercise218.kMap_comp_hMap


namespace DomainTheory.Neighborhood.Exercise218

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap















/-- **Exercise 2.18 — `h` is not an isomorphism.** It is not surjective: `↑(01Σ*)` is not in the
range (any preimage `x` satisfies `x = k(h(x))`, forcing `h(x) = ↑(00Σ*) ≠ ↑(01Σ*)`). -/
theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone

end DomainTheory.Neighborhood.Exercise218
