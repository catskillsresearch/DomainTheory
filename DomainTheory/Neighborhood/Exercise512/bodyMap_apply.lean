/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise512.Basic


namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- Value of the loop body: `M(w, x) = cond(p(x), w(f(x)), x)`. -/
theorem bodyMap_apply (w : (funSpace V V).Element) (x : V.Element) :
    (bodyMap V p f).toElementMap (pair w x) =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [bodyMap, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.Neighborhood.Exercise512
