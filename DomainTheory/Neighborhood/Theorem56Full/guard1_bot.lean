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
public import DomainTheory.Neighborhood.Theorem56Full.T_bot_eq
public import DomainTheory.Neighborhood.Theorem56Full.guard1_apply

@[expose] public section


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)












theorem guard1_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : component z j = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rw [guard1_apply, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end DomainTheory.Neighborhood.Theorem56Full
