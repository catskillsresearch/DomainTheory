/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem41.Basic
import DomainTheory.Neighborhood.Theorem41.fixMap_toElementMap_principal
import DomainTheory.Neighborhood.Theorem41.exists_principal_iterMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗).** The elementwise action of `fix` is
the least fixed point of the corresponding map: `fix.toElementMap φ = fix(toApproxMap φ)`. The
forward inclusion (`⊆ x`) is `exists_principal_iterMap`; the reverse is monotonicity of `fix` along
`↑W ⊑ toApproxMap φ`. -/
theorem fixMap_toElementMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ = (toApproxMap φ).fixElement := by
  apply Element.ext
  intro X
  rw [toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨W, hw, hmem⟩
    rw [fixMap_toElementMap_principal] at hmem
    have hle : (funSpace V V).principal (φ.sub hw) ≤ φ :=
      fun Z hZ => φ.up_mem hw hZ.1 hZ.2
    exact fixElement_mono ((funSpaceEquiv V V).monotone hle) X hmem
  · rintro ⟨n, hn⟩
    obtain ⟨W, hw, hWn⟩ := exists_principal_iterMap V φ n X hn
    refine ⟨W, hw, ?_⟩
    rw [fixMap_toElementMap_principal]
    exact ⟨n, hWn⟩

end DomainTheory.Neighborhood
