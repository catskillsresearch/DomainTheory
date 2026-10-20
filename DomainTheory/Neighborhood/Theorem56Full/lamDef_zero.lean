/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise511
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.Neighborhood.Theorem56Full.Basic
public import DomainTheory.Neighborhood.Theorem56Full.lamDef_total

@[expose] public section


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)


















/-- `zero : Vector ℕ 0 → ℕ`, the constant `0` (nullary). -/
theorem lamDef_zero : LamDef (strictGuardN 0 (constMap 𝒩 (natElem 0)))
    ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : List.Vector ℕ 0 →. ℕ) :=
  lamDef_total (constMap 𝒩 (natElem 0)) _ (fun v => by rw [toElementMap_constMap])

end DomainTheory.Neighborhood.Theorem56Full
