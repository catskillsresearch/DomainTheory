/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise508.Basic
import DomainTheory.Neighborhood.Exercise508.toApproxMap_toFilter


namespace DomainTheory.Neighborhood.Exercise508

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}










/-- `I(x) = x`. -/
theorem Ielem_apply (X : Dom) (x : X.sys.Element) :
    (toApproxMap (Ielem X)).toElementMap x = x := by
  rw [Ielem, toApproxMap_toFilter, toElementMap_idMap]

end DomainTheory.Neighborhood.Exercise508
