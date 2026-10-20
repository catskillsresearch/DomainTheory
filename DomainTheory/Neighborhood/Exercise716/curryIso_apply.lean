/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise716.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}


/-- `curryIso V₀ V₁ V₂` sends a filter `x` to the filter of the curried least map (by definition). -/
theorem curryIso_apply (x : (funSpace (prod V₀ V₁) V₂).Element) :
    curryIso V₀ V₁ V₂ x = toFilter (curry (toApproxMap x)) := rfl

end DomainTheory.Neighborhood
