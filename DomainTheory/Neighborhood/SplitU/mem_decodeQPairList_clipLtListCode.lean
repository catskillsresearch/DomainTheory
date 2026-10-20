/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.decodeRatPair_clipLtCode
import DomainTheory.Neighborhood.SplitU.decodeQPairList_singletonCode


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem










theorem mem_decodeQPairList_clipLtListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipLtListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipLt (decodeRat m) p0 := by
  unfold clipLtListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode]; exact hp⟩

end DomainTheory.Neighborhood
