/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

end DomainTheory.Neighborhood
