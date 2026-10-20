/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise816
import DomainTheory.Neighborhood.Exercise823.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}










/-- **`‖t‖` is a genuine (not merely approximate) fixed point of `t`.** -/
theorem tOp_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    tOp t (fixOp t) = fixOp t := by
  show toApproxMap (t.toElementMap (toFilter (toApproxMap t.fixElement))) = toApproxMap t.fixElement
  rw [toFilter_toApproxMap, toElementMap_fixElement]

end Exercise823
end DomainTheory.Neighborhood
