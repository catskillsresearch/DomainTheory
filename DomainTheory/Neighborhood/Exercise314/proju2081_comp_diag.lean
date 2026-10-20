/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise314.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)




theorem proj₁_comp_diag : (proj₁ V V).comp (diag V) = idMap V :=
  proj₁_comp_paired (idMap V) (idMap V)

end DomainTheory.Neighborhood
