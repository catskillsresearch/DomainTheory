/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.LevelSetPrimrec.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem











theorem myTestBit_le_one (m ℓ : ℕ) : myTestBit m ℓ ≤ 1 := by
  unfold myTestBit
  rcases Nat.mod_two_eq_zero_or_one (myDivPow2 m ℓ) with h | h <;> omega

end DomainTheory.Neighborhood
