/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516ThueMorse
import DomainTheory.Neighborhood.Exercise516Overlap.Basic
import DomainTheory.Neighborhood.Exercise516Overlap.no_overlap


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood






/-- **The Thue–Morse sequence is cube-free.** A cube of period `p ≥ 1` (the factor `a·a·a` with
`|a| = p`) is in particular an overlap, so none exists. -/
theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩

end DomainTheory.Neighborhood.Exercise516
