/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23.Basic


namespace DomainTheory.Neighborhood.Example23

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB









/-- **A leading `01` always commits to `false`, whatever follows.** `scan([0,1]++τ) = false`, for
*every* tail `τ`. (Exercise 2.16's second equation, at the token level.) -/
theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]

end DomainTheory.Neighborhood.Example23
