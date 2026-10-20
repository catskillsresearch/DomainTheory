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
import DomainTheory.Neighborhood.Theorem56Full.eq_of_component_eq
import DomainTheory.Neighborhood.Theorem56Full.component_push_zero
import DomainTheory.Neighborhood.Theorem56Full.component_push_succ
import DomainTheory.Neighborhood.Theorem56Full.component_bot


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)




























theorem oneArg_bot : (oneArg).toElementMap N.bot = 𝒩.bot := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  apply eq_of_component_eq
  intro i
  cases i with
  | zero => rw [component_push_zero, component_bot]
  | succ k => rw [component_push_succ, component_bot, component_bot]

end DomainTheory.Neighborhood.Theorem56Full
