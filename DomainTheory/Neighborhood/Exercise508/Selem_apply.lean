/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise508.Basic
import DomainTheory.Neighborhood.Exercise508.toApproxMap_toFilter
import DomainTheory.Neighborhood.Exercise508.Smap_apply


namespace DomainTheory.Neighborhood.Exercise508

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}


variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}










/-- `S(F)(G)(x) = F(x)(G(x))`. -/
theorem Selem_apply (X A B : Dom)
    (F : (X.arrow (A.arrow B)).sys.Element) (G : (X.arrow A).sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap ((toApproxMap (Selem X A B)).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Selem, toApproxMap_toFilter]
  exact Smap_apply F G x

end DomainTheory.Neighborhood.Exercise508
