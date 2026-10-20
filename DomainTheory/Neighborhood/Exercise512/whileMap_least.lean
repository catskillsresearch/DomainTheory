/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise512.Basic
import DomainTheory.Neighborhood.Exercise512.Wop_apply


namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)





/-- **Leastness.** Any `w'` satisfying the `while`-recursion `w'(x) = cond(p(x), w'(f(x)), x)`
dominates the least solution `whileMap`. -/
theorem whileMap_least (w' : (funSpace V V).Element)
    (hw' : ∀ x : V.Element, (toApproxMap w').toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w').toElementMap (f.toElementMap x)) x))) :
    whileFix V p f ≤ w' := by
  apply fixElement_le_of_toElementMap_le
  apply le_of_eq
  apply (funSpaceEquiv V V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro x
  rw [Wop_apply]
  exact (hw' x).symm
end DomainTheory.Neighborhood.Exercise512
