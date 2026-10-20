/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Theorem86.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **The easy half of Theorem 8.6's range characterization.** If `f` is a fixed point of `sub`,
then `f` is a finitary projection: `sub f = f` says exactly that `f` *is*
`retractionOfSubsystem (fixedNbhd_subsystem f)`, and Definition 8.3's corollary of Proposition 8.2
finishes immediately. (The converse — every finitary projection is a fixed point of `sub` — is
Theorem 8.5's harder direction; see the module docstring.) -/
theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    IsFinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)

end DomainTheory.Neighborhood
