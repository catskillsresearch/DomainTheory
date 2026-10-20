/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise115.Basic
import DomainTheory.Neighborhood.Exercise115.flat_empty_not_mem
import DomainTheory.Neighborhood.Exercise115.flat_mem_singleton


namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem








/-- **Flat classification.** Every element is `⊥` or an atom `↑{n}`. *Classical.* -/
theorem flat_classify (x : flat.Element) :
    x = flat.bot ∨ ∃ n, x = flat.principal (flat_mem_singleton n) := by
  classical
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    have huniq : ∀ m, x.mem {m} → m = n := by
      intro m hm
      by_contra hmn
      have hi : x.mem (({m} : Set ℕ) ∩ {n}) := x.inter_mem hm hn
      rw [singleton_disjoint hmn] at hi
      exact flat_empty_not_mem (x.sub hi)
    apply Element.ext
    intro W
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · exact ⟨Or.inl rfl, Set.subset_univ _⟩
      · obtain rfl := huniq k hx
        exact ⟨flat_mem_singleton k, subset_rfl⟩
    · rintro ⟨hWmem, hsub⟩
      exact x.up_mem hn hWmem hsub
  · refine Or.inl ?_
    apply Element.ext
    intro W
    rw [flat.mem_bot]
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd ⟨k, hx⟩ h
    · rintro rfl
      exact x.master_mem

end DomainTheory.Neighborhood.Exercise115
