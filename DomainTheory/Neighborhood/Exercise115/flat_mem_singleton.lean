/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise115.Basic


namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem








/-- The atom `↑{n}` (a finite element). -/
theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

end DomainTheory.Neighborhood.Exercise115
