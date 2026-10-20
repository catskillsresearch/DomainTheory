/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace



























theorem fcapGdeltaPack_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fcapGdeltaPack f g) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · have : 0 ∈ scottUnion f x := by rw [← hf x]; exact h0
      obtain ⟨p, hp, hp0⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inl ⟨hk0, hp0⟩⟩
    · have : n ∈ scottUnion g x := by rw [← hg x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inr ⟨n, hk, hnp⟩⟩
  · intro hk
    obtain ⟨p, hp, h⟩ := mem_scottUnion.mp hk
    rcases h with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · exact Or.inl ⟨hk0, isScottContinuous_monotone hf hp h0⟩
    · exact Or.inr ⟨n, hk, isScottContinuous_monotone hg hp hn⟩

end DomainTheory.DataTypesAsLattices
