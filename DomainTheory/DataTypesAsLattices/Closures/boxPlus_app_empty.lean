/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- Occupancy test of (5.13): neither component inhabited, so the value is `⊥`. -/
theorem boxPlus_app_empty {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u = botElem := by
  rw [boxPlus_app, hx, hy, boxTag_bot, boxTag_bot, Set.union_self, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
