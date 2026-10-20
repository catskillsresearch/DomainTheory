/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition87
public import DomainTheory.Neighborhood.RationalPrimrec
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive












theorem mem_combineIntervals {L1 L2 : List (ℚ × ℚ)} {p : ℚ × ℚ} :
    p ∈ combineIntervals L1 L2 ↔ ∃ p1 ∈ L1, ∃ p2 ∈ L2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold combineIntervals
  rw [List.mem_flatMap]
  simp only [List.mem_map, eq_comm]

end DomainTheory.Neighborhood
