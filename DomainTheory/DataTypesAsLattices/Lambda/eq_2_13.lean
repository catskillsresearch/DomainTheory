/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




























/-- **Scott 1976, (2.13).** Application distributes over arbitrary unions. -/
theorem eq_2_13 (F : Set Pomega) (x : Pomega) :
    funOf (⋃₀ F) x = ⋃ u ∈ F, funOf u x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨u, hu, hpu⟩ := Set.mem_sUnion.mp hp
    exact Set.mem_iUnion₂.mpr ⟨u, hu, n, hn, hpu⟩
  · intro hm
    obtain ⟨u, hu, n, hn, hp⟩ := Set.mem_iUnion₂.mp hm
    exact ⟨n, hn, ⟨u, hu, hp⟩⟩

end DomainTheory.DataTypesAsLattices
