/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_of_empty {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = botElem := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
    · exact (h0 hz).elim
    · exact (hp ht).elim
  · intro hn
    simp [botElem] at hn

end DomainTheory.DataTypesAsLattices
