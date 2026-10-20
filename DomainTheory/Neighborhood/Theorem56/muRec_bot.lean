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
import DomainTheory.Neighborhood.Theorem56.T_bot_eq
import DomainTheory.Neighborhood.Theorem56.muRec_rec


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)












section Mu

variable (f : ApproximableMap (prod N N) N)





/-- **μ is strict in the test.** If `f(n̂, m̂) = ⊥`, the search diverges. -/
theorem muRec_bot {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = N.bot) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = N.bot := by
  rw [muRec_rec, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end Mu
end DomainTheory.Neighborhood.Theorem56
