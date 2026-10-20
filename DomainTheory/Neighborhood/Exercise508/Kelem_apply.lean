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










/-- `K(c)(x) = c`. -/
theorem Kelem_apply (A X : Dom) (c : A.sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap (Kelem A X)).toElementMap c)).toElementMap x = c := by
  rw [Kelem, toApproxMap_toFilter]
  have h := toElementMap_curry_apply (proj₀ A.sys X.sys) c x
  rw [toElementMap_proj₀, fst_pair] at h
  exact h

end DomainTheory.Neighborhood.Exercise508
