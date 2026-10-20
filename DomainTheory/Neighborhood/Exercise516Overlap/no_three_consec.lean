/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516ThueMorse
import DomainTheory.Neighborhood.Exercise516Overlap.Basic
import DomainTheory.Neighborhood.Exercise516Overlap.odd_of_consec_eq


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood


/-- **No three consecutive equal symbols** (the period-`1` case): `¬ (tm j = tm (j+1) ∧
tm (j+1) = tm (j+2))`. If both held, `j` and `j+1` would both be odd. -/
theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega

end DomainTheory.Neighborhood.Exercise516
