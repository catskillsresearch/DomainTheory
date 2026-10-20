/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Theorem111
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise113.Basic
import DomainTheory.Neighborhood.Exercise113.branch_mem_iff
import DomainTheory.Neighborhood.Exercise113.prefix_comparable_of_mem


namespace DomainTheory.Neighborhood.Exercise113

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- **Exercise 1.13 (total elements).** Each infinite path `p` gives a *total* (maximal) element
`branch p`: any `y` it approximates approximates it back. (These maximal elements are exactly the
limit nodes along the top of the binary-tree picture.) -/
theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]⟩

end DomainTheory.Neighborhood.Exercise113
