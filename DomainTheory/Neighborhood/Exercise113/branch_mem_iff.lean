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


namespace DomainTheory.Neighborhood.Exercise113

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- `cone σ ∈ branch p` iff `σ` is an initial segment of some `p ↾ n`, i.e. `σ` lies on the path. -/
theorem branch_mem_iff (p : ℕ → Bool) {σ : Str} :
    (branch p).mem (cone σ) ↔ ∃ n, σ <+: prefixSeq p n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mp h
    exact ⟨n, cone_subset_cone.mp hn.2⟩
  · rintro ⟨n, hn⟩
    exact (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mpr
      ⟨n, memB_cone σ, cone_subset_cone.mpr hn⟩

end DomainTheory.Neighborhood.Exercise113
