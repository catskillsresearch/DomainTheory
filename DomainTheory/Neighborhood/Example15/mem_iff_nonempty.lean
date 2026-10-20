/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import DomainTheory.Neighborhood.Example15.Basic


namespace DomainTheory.Neighborhood.Example15

open NeighborhoodSystem









/-- The neighbourhoods of Example 1.5 are exactly the non-empty subsets. -/
theorem mem_iff_nonempty (X : Set Token) : neighborhoodSystem.mem X ↔ X.Nonempty := Iff.rfl

end DomainTheory.Neighborhood.Example15
