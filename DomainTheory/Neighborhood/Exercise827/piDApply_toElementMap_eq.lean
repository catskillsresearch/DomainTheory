/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap
































/-- Evaluating `piDApply d f` at an already-`subU`-projected point simplifies (via `subU`'s
idempotency) exactly to `toElementMap_piDApply`'s formula with `t` replaced by `subU.toElementMap
t` throughout. The key computational step behind `isRetraction_piD`. -/
theorem piDApply_toElementMap_eq (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap (subU.toElementMap t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, toElementMap_idem_of_isRetraction isProjection_subU.1 t]

end DomainTheory.Neighborhood
