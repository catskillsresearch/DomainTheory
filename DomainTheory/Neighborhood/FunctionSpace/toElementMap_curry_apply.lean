/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

















































variable {V₂ : NeighborhoodSystem γ}









/-- **Theorem 3.12(i) (Scott 1981, PRG-19).** `curry(g)(x)(y) = g(x, y)`. -/
theorem toElementMap_curry_apply (g : ApproximableMap (prod V₀ V₁) V₂)
    (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hyY, X, hxX, hX, _, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
    exact ⟨Y, hyY, X, hxX, x.sub hxX, step_mem (y.sub hyY) (g.rel_cod hrel), hrel⟩

end DomainTheory.Neighborhood
