/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.LevelSetPrimrec
import DomainTheory.Neighborhood.MinLevel
import DomainTheory.Neighborhood.SplitV.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive







/-- **`myFirstBit` never overshoots its bound.** -/
theorem myFirstBit_le (m N : ℕ) : myFirstBit m N ≤ N := by
  rcases myFirstBit_spec m N with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega

end DomainTheory.Neighborhood
