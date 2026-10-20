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
import DomainTheory.Neighborhood.Theorem56Full.component_vecElem_lt
import DomainTheory.Neighborhood.Theorem56Full.lamDef_total


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)


















/-- `succ : Vector ℕ 1 → ℕ`, `v ↦ v.head + 1`. -/
theorem lamDef_succ : LamDef (strictGuardN 1 (succMap.comp (projN N 0)))
    ((fun v => Nat.succ v.head : List.Vector ℕ 1 → ℕ) : List.Vector ℕ 1 →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_comp, toElementMap_projN, component_vecElem_lt v (by norm_num),
      succMap_natElem]
    congr 1
    simp [List.Vector.get_zero])

end DomainTheory.Neighborhood.Theorem56Full
