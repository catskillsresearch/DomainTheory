/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Exercise216.Basic


namespace DomainTheory.Neighborhood.Exercise216

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB


/-- **Exercise 2.16.** The elementwise action of `sigmaMap σ` is Scott's `σx`: `(sigmaMap σ)(x) =
σx` for every `x ∈ |B|`. -/
theorem toElementMap_sigmaMap (σ : Str) (x : B.Element) :
    (sigmaMap σ).toElementMap x = sigmaElt σ x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hxX, _, hY, hsub⟩
    exact ⟨hY, X, hxX, hsub⟩
  · rintro ⟨hY, X, hxX, hsub⟩
    exact ⟨X, hxX, x.sub hxX, hY, hsub⟩

end DomainTheory.Neighborhood.Exercise216
