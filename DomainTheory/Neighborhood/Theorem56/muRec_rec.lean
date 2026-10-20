/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Theorem56.Basic
import DomainTheory.Neighborhood.Theorem56.muBody_apply


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)












section Mu

variable (f : ApproximableMap (prod N N) N)





/-- The defining recursion of `muRec`. -/
theorem muRec_rec (x y : N.Element) :
    (muRec f).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((muRec f).toElementMap (pair (succMap.toElementMap x) y)))) := by
  have hfix : (muOp f).toElementMap (muOp f).fixElement = (muOp f).fixElement :=
    toElementMap_fixElement (muOp f)
  have hval := toElementMap_curry_apply (muBody f) (muOp f).fixElement (pair x y)
  rw [← muOp, hfix] at hval
  rw [muRec, hval, muBody_apply]

end Mu
end DomainTheory.Neighborhood.Theorem56
