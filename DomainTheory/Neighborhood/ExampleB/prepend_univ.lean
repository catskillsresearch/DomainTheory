/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.List.Infix
import DomainTheory.Neighborhood.ExampleB.Basic


namespace DomainTheory.Neighborhood.ExampleB

open DomainTheory.Neighborhood NeighborhoodSystem

















/-- `σΣ* = σ·Σ*`: prepending `σ` to the whole space recovers the cone of `σ`. -/
theorem prepend_univ (σ : Str) : prepend σ Set.univ = cone σ := by
  ext w
  simp only [mem_prepend, Set.mem_univ, true_and, mem_cone]
  constructor
  · rintro ⟨τ, rfl⟩
    exact List.prefix_append σ τ
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

end DomainTheory.Neighborhood.ExampleB
