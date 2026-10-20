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
import DomainTheory.Neighborhood.Theorem56.muRec_rec


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)












section Mu

variable (f : ApproximableMap (prod N N) N)





/-- **μ, step.** If `f(n̂, m̂)` is a positive total `(j+1)^`, the search advances to `n+1`. -/
theorem muRec_step {n m j : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem (j + 1)) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) =
      (muRec f).toElementMap (pair (natElem (n + 1)) (natElem m)) := by
  rw [muRec_rec, h, zeroMap_natElem_succ, Exercise326.cond_false, succMap_natElem]

end Mu
end DomainTheory.Neighborhood.Theorem56
