/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices































/-- Graph expansiveness `I ⊆ λx. f(x)` is value-expansiveness on finite sets. -/
theorem Icomb_subset_graph {f : Pomega → Pomega} :
    Icomb ⊆ graph f ↔ ∀ n, e n ⊆ f (e n) := by
  constructor
  · intro h n m hm
    have := h ⟨n, m, rfl, hm⟩
    rcases this with ⟨n', m', heq, hm'⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact hm'
  · intro h p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, h n hm⟩

end DomainTheory.DataTypesAsLattices
