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
















theorem levelSet_inter_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ ∩ levelSet k m₂ = levelSet k (m₁ &&& m₂) := by
  ext n; simp [levelSet, Nat.testBit_and]

end DomainTheory.Neighborhood
