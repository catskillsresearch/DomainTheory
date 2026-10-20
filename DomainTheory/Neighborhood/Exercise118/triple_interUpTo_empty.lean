/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise118.Basic
import DomainTheory.Neighborhood.Exercise118.triSys_master


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood






namespace triSys




theorem triple_interUpTo_empty : triSys.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo_succ, NeighborhoodSystem.interUpTo_zero, triSys_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

end triSys
end DomainTheory.Neighborhood
