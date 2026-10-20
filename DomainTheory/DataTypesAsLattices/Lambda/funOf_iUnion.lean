/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices




























theorem funOf_iUnion (xs : ℕ → Pomega) (x : Pomega) :
    funOf (⋃ n, xs n) x = ⋃ n, funOf (xs n) x := by
  ext m
  constructor
  · intro ⟨n, hn, hk⟩
    obtain ⟨k, hmem⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k, ⟨n, hn, hmem⟩⟩
  · intro hm
    obtain ⟨k, ⟨n, hn, hmem⟩⟩ := Set.mem_iUnion.mp hm
    exact ⟨n, hn, Set.mem_iUnion.mpr ⟨k, hmem⟩⟩

end DomainTheory.DataTypesAsLattices
