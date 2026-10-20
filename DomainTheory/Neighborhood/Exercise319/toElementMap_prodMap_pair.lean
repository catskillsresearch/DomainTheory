/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise319.Basic
import DomainTheory.Neighborhood.Exercise319.toElementMap_prodMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.19(i) (Scott 1981, PRG-19).** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`. -/
theorem toElementMap_prodMap_pair (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (x : V₀.Element) (y : V₁.Element) :
    (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y) := by
  rw [toElementMap_prodMap, fst_pair, snd_pair]

end DomainTheory.Neighborhood
