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








/-- `affine k ℓ` itself is the singleton-bitmask `levelSet`. -/
theorem affine_eq_levelSet (k ℓ : ℕ) : affine k ℓ = levelSet k (2 ^ ℓ) := by
  ext n
  simp [mem_affine, mem_levelSet, Nat.testBit_two_pow, eq_comm]

end DomainTheory.Neighborhood
