/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example44
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise419.Basic
public import DomainTheory.Neighborhood.Exercise419.condT_bot

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44






variable {β : Type*}


















/-- **Exercise 4.19 (Scott 1981, PRG-19).** The same defining equation holds on every partial
element `σ⊥` — including `⊥ = []⊥` where `empty(⊥) = ⊥` forces `cond(⊥, …) = ⊥`. -/
theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]

end DomainTheory.Neighborhood.Exercise419
