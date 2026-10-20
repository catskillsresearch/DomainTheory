/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.toElementMap_piDTypeMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































/-- `piDApply`'s defining formula, restated via `piDType`/`piDTypeMap`. -/
theorem toElementMap_piDApply' (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (piDType d (subU.toElementMap t)).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, piDType, toElementMap_piDTypeMap]

end DomainTheory.Neighborhood
