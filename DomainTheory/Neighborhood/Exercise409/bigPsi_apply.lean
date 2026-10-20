/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise409.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-- **Exercise 4.9 (Scott 1981, PRG-19).** The defining equation `Ψ(θ)(f) = f(θ(f))`. -/
theorem bigPsi_apply (V : NeighborhoodSystem α)
    (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element) :
    (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
      = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f) := by
  rw [bigPsi, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply, evalMap_apply]

end DomainTheory.Neighborhood
