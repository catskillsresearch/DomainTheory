/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise511.Basic


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)





theorem unfold_fold (p : (prod V (iterSys V)).Element) :
    (unfold V).toElementMap ((fold V).toElementMap p) = p := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply]

end DomainTheory.Neighborhood.Exercise511
