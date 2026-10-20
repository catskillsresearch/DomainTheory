/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example62
public import DomainTheory.Neighborhood.Example44
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Exercise822.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822



/-- **`B` is a literal subsystem of `C`** (Definition 6.10): every `B`-neighbourhood is already a
`C`-neighbourhood, and consistency is inherited — if two cones intersect to a `C`-neighbourhood
(hence nonempty), `cone_trichotomy` rules out the disjoint case, so the intersection is already the
smaller of the two cones. -/
theorem B_subsystem_C : B ◁ C where
  master_eq := rfl
  sub := by rintro X ⟨σ, rfl⟩; exact memC_cone σ
  inter_closed := by
    rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩ hCXY
    rcases cone_trichotomy σ τ with h | h | h
    · rw [Set.inter_eq_left.mpr h]; exact ⟨σ, rfl⟩
    · rw [Set.inter_eq_right.mpr h]; exact ⟨τ, rfl⟩
    · rw [h] at hCXY; exact absurd (C_nonempty ∅ hCXY) (by simp)

end Exercise822
end DomainTheory.Neighborhood
