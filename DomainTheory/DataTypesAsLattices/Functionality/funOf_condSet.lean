/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices





















theorem funOf_condSet (z x y w : Pomega) :
    funOf (condSet z x y) w = condSet z (funOf x w) (funOf y w) := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with ⟨hx, h0⟩ | ⟨hy, ht⟩
    · exact Or.inl ⟨⟨n, hn, hx⟩, h0⟩
    · exact Or.inr ⟨⟨n, hn, hy⟩, ht⟩
  · intro hm
    rcases hm with ⟨⟨n, hn, hx⟩, h0⟩ | ⟨⟨n, hn, hy⟩, ht⟩
    · exact ⟨n, hn, Or.inl ⟨hx, h0⟩⟩
    · exact ⟨n, hn, Or.inr ⟨hy, ht⟩⟩

end DomainTheory.DataTypesAsLattices
