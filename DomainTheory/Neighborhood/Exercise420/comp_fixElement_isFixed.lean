/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise420.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f(fix(g ∘ f))` is a fixed point of `f ∘ g`:
`(f ∘ g)(f(fix(g∘f))) = f((g∘f)(fix(g∘f))) = f(fix(g∘f))`. -/
theorem comp_fixElement_isFixed (f g : ApproximableMap V V) :
    (f.comp g).toElementMap (f.toElementMap (g.comp f).fixElement)
      = f.toElementMap (g.comp f).fixElement := by
  rw [toElementMap_comp]
  -- `g(f(fix(g∘f))) = (g∘f)(fix(g∘f)) = fix(g∘f)`
  have h : g.toElementMap (f.toElementMap (g.comp f).fixElement) = (g.comp f).fixElement := by
    rw [← toElementMap_comp]
    exact toElementMap_fixElement (g.comp f)
  rw [h]

end ApproximableMap
end DomainTheory.Neighborhood
