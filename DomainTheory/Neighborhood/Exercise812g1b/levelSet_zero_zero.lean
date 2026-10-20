/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.LevelSetPrimrec
import DomainTheory.Neighborhood.Exercise812g1b.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem levelSet_zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

end DomainTheory.Neighborhood
