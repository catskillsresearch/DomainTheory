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








theorem mem_decodeQPairList (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList c ↔ ∃ e ∈ decodeList c, p = decodeRatPair e := by
  unfold decodeQPairList; rw [List.mem_map]; simp [eq_comm]

end DomainTheory.Neighborhood
