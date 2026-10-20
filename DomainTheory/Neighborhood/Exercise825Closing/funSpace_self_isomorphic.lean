/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise825Congr
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise825Closing.Basic
import DomainTheory.Neighborhood.Exercise825Closing.prod_self_isomorphic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {V : NeighborhoodSystem β}

/-- **Closing argument, step 2 (Exercise 8.25's main equation).** `D ≅ D → V` and `V × V ≅ V`
imply `D ≅ D → D`. -/
theorem funSpace_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    D ≅ᴰ funSpace D D :=
  have hDD : prod D D ≅ᴰ D := prod_self_isomorphic hDV hVV
  have step : funSpace D D ≅ᴰ D :=
    ((funSpace_congr_right hDV).trans (curry_isomorphic D D V).symm).trans
      ((funSpace_congr_left hDD).trans hDV.symm)
  step.symm

end DomainTheory.Neighborhood
