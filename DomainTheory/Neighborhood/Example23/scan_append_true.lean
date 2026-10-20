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









/-- **A leading `1` always commits to `true`, whatever follows.** `scan([1]++τ) = true`, for
*every* tail `τ`. (Exercise 2.16's first equation, at the token level.) -/
theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

end DomainTheory.Neighborhood.Example23
