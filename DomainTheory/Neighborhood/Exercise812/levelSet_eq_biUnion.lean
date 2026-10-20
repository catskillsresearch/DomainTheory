/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.Theorem85
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import DomainTheory.Neighborhood.Exercise812.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem








/-- `levelSet k m` is exactly the union of `affine k ℓ` over `ℓ` with `m.testBit ℓ`. -/
theorem levelSet_eq_biUnion (k m : ℕ) :
    levelSet k m = ⋃ ℓ ∈ (Finset.range (2 ^ k)).filter (fun ℓ => m.testBit ℓ), affine k ℓ := by
  ext n
  simp only [mem_levelSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, mem_affine,
    exists_prop]
  constructor
  · intro h; exact ⟨n % 2 ^ k, ⟨Nat.mod_lt n (by positivity), h⟩, rfl⟩
  · rintro ⟨ℓ, ⟨-, hm⟩, rfl⟩; exact hm

end DomainTheory.Neighborhood
