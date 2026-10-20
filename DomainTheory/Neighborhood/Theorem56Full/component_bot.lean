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


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)



















/-- Coordinates of the bottom stack are `⊥`. -/
theorem component_bot (i : ℕ) : component (𝒩.bot) i = N.bot := by
  have hbot : (𝒩.bot) = ofSeq (fun _ => N.bot) :=
    le_antisymm (𝒩.bot_le _)
      (le_of_component_le (fun i => by rw [component_ofSeq]; exact N.bot_le _))
  rw [hbot, component_ofSeq]

end DomainTheory.Neighborhood.Theorem56Full
