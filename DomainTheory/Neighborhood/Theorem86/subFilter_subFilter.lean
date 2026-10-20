/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Theorem86.Basic
import DomainTheory.Neighborhood.Theorem86.sub_sub


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6















theorem subFilter_subFilter (φ : (funSpace E E).Element) :
    subFilter (subFilter φ) = subFilter φ := by
  unfold subFilter
  rw [toApproxMap_toFilter, sub_sub]

end Sub8_6
end DomainTheory.Neighborhood
