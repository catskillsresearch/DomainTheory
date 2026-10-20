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





















































theorem toElementMap_piDTypeMap (d : ApproximableMap U U) (s : U.Element) :
    (piDTypeMap d).toElementMap s = jArrow.toElementMap (subU.toElementMap (d.toElementMap s)) := by
  unfold piDTypeMap
  rw [toElementMap_comp, toElementMap_comp]

end DomainTheory.Neighborhood
