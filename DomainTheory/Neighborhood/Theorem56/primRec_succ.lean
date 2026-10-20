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
import DomainTheory.Neighborhood.Theorem56.primRec_rec


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)










section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)




/-- **Primitive recursion, step case.** `h̄((n+1)^, m̂) = g(n̂, m̂, h̄(n̂, m̂))`. -/
theorem primRec_succ (n m : ℕ) :
    (primRec f g).toElementMap (pair (natElem (n + 1)) (natElem m)) =
      g.toElementMap
        (pair (natElem n)
          (pair (natElem m) ((primRec f g).toElementMap (pair (natElem n) (natElem m))))) := by
  rw [primRec_rec, zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ]

end PrimRec
end DomainTheory.Neighborhood.Theorem56
