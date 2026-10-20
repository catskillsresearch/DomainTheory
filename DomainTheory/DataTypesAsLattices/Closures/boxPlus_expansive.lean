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
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_mono
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_bot_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 (sum half), expansiveness.** Each of the four
occupancy cases of (5.13) is expansive: on a one-sided `u` the shift `a'`
is expansive by `boxShift_expansive` and (5.8) rebuilds `u`, while mixed
`u` goes to `⊤` and empty `u` is `⊥`. -/
theorem boxPlus_expansive {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b)
    (u : Pomega) : u ⊆ funOf (boxPlus a b) u := by
  have h8 : squarePair (squareFst u) (squareSnd u) = u := eq_5_8 u
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [hx, hy, squarePair_bot_bot] at h8
    rw [boxPlus_app_empty hx hy, ← h8]
  · rw [boxPlus_app_right hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
      rw [hx]
      exact squarePair_mono subset_rfl (boxShift_expansive hb (squareSnd u))
    rwa [h8] at hsub
  · rw [boxPlus_app_left hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair (funOf (boxShift a) (squareFst u)) botElem := by
      rw [hy]
      exact squarePair_mono (boxShift_expansive ha (squareFst u)) subset_rfl
    rwa [h8] at hsub
  · rw [boxPlus_app_mixed hx hy]
    exact fun k _ => Set.mem_univ k

end DomainTheory.DataTypesAsLattices
