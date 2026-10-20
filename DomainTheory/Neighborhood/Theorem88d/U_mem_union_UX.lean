/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88b
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)



theorem U_mem_union_UX (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨-, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨-, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨decodeQPairList (canonCode n) ++ decodeQPairList (canonCode m),
      (presentedIntervals_append _ _).symm⟩, hne1.mono Set.subset_union_left,
    Set.union_subset hsub1 hsub2⟩

end DomainTheory.Neighborhood
