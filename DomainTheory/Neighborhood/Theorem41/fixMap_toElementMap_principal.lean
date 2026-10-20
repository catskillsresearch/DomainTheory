/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem41.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- On a finite element `↑F`, `fix` returns `fix(↑F)` (the least fixed point of the least map of
`F`). -/
theorem fixMap_toElementMap_principal (V : NeighborhoodSystem α)
    {W : Set (ApproximableMap V V)} (hW : (funSpace V V).mem W) :
    (fixMap V).toElementMap ((funSpace V V).principal hW) =
      (toApproxMap ((funSpace V V).principal hW)).fixElement :=
  toElementMap_ofMono_principal _ _ W hW

end DomainTheory.Neighborhood
