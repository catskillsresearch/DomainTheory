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




theorem affine_eq_empty_of_ge {k ℓ : ℕ} (hℓ : 2 ^ k ≤ ℓ) : affine k ℓ = ∅ := by
  ext n
  simp only [mem_affine, Set.mem_empty_iff_false, iff_false]
  intro h
  have hlt : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (by positivity)
  omega

end DomainTheory.Neighborhood
