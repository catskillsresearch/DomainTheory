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


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap



























/-- `(prependMap σ).toElementMap y = σ · y`: the approximable-map action agrees with Scott's
multiplication `mulElem`, using `{σ} ⊆ X` (any valid witness `X` for `emb σ` contains `σ`) to
tighten the witness set to `{σ}` without loss. -/
theorem prependMap_toElementMap (σ : List Bool) (y : Ssys.Element) :
    (prependMap σ).toElementMap y = mulElem (emb σ) y := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hY, hInSY, hInSZ, hsub⟩
    exact ⟨hInSZ, {σ}, ⟨InS.singleton σ, rfl⟩, Y, hY, hsub⟩
  · rintro ⟨hInSZ, X, ⟨_, hσX⟩, Y, hY, hsub⟩
    refine ⟨Y, hY, y.sub hY, hInSZ, ?_⟩
    exact (concat_mono (Set.singleton_subset_iff.mpr hσX) (Set.Subset.refl _)).trans hsub

end Exercise722
end DomainTheory.Neighborhood
