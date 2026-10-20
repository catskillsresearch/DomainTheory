/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise715
import DomainTheory.Neighborhood.Exercise825Pow
import DomainTheory.Neighborhood.Exercise825Embed
import DomainTheory.Neighborhood.Exercise825Closing
import DomainTheory.Neighborhood.Exercise820
import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic
import DomainTheory.Neighborhood.Exercise825FixedPoint.toApproxMap_lamOp


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

















/-- **`tOp (tOpMap c) a = arrowComb a c`**, for every `a`: `t` really does implement
`a ↦ arrowComb a c`, continuously. -/
theorem tOp_tOpMap (c a : ApproximableMap U U) :
    Exercise823.tOp (tOpMap c) a = arrowComb a c := by
  show toApproxMap ((tOpMap c).toElementMap (toFilter a)) = arrowComb a c
  rw [tOpMap, toElementMap_comp, toApproxMap_toElementMap_expMap, toApproxMap_lamOp,
    expMap_eq_lamComb]
  rfl

end DomainTheory.Neighborhood
