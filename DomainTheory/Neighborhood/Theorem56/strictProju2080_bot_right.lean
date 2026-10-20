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
import DomainTheory.Neighborhood.Theorem56.strictProju2080_apply


namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)




/-- Strict in the second argument: `proj₀(n̂, ⊥) = ⊥`. -/
theorem strictProj₀_bot_right (n : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) N.bot) = N.bot := by
  rw [strictProj₀_apply, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end DomainTheory.Neighborhood.Theorem56
