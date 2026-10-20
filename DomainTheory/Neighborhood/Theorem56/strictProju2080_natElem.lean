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
import DomainTheory.Neighborhood.Theorem56.strictProju2080_apply


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)




/-- `proj₀(n̂, m̂) = n̂`. -/
theorem strictProj₀_natElem (n m : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]

end DomainTheory.Neighborhood.Theorem56
