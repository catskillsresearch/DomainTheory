/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis
import DomainTheory.Neighborhood.Theorem56Full.Basic
import DomainTheory.Neighborhood.Theorem56Full.findBody_apply


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























section Rfind

variable (φf : ApproximableMap 𝒩 N)




/-- The defining recursion equation of the search. -/
theorem searchMap_rec (z : 𝒩.Element) :
    (searchMap φf).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((searchMap φf).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have hfix : (findOp φf).toElementMap (findOp φf).fixElement = (findOp φf).fixElement :=
    toElementMap_fixElement (findOp φf)
  have hval := toElementMap_curry_apply (findBody φf) (findOp φf).fixElement z
  rw [← findOp, hfix] at hval
  rw [searchMap, hval, findBody_apply]

end Rfind
end DomainTheory.Neighborhood.Theorem56Full
