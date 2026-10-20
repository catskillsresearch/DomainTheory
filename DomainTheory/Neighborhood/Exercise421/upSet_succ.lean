/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414







/-- `[m⁺] = [m]⁺`: the recursion step of 4.13(3). -/
theorem upSet_succ (m : ℕ) : upSet (m + 1) = succImage (upSet m) := by
  ext k
  simp only [upSet, succImage, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

end DomainTheory.Neighborhood.Exercise421
