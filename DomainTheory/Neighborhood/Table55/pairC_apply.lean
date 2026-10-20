/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Table55.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








theorem pairC_apply (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((pairC V₀ V₁).toElementMap x)).toElementMap y = pair x y := by
  rw [pairC, toElementMap_curry_apply, toElementMap_idMap]

end DomainTheory.Neighborhood
