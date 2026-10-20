/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.mem_decodeQPairList_appendCode


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem presentedIntervals_decodeQPairList_appendCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (appendCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∪ presentedIntervals (decodeQPairList c2) := by
  ext x
  simp only [mem_presentedIntervals, Set.mem_union]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rcases (mem_decodeQPairList_appendCode c1 c2 p).mp hp with hp' | hp'
    · exact Or.inl ⟨p, hp', h1, h2⟩
    · exact Or.inr ⟨p, hp', h1, h2⟩
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inl hp), h1, h2⟩
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inr hp), h1, h2⟩

end DomainTheory.Neighborhood
