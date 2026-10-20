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
import DomainTheory.Neighborhood.Theorem86.isFinitaryProjection_of_sub_eq_self
import DomainTheory.Neighborhood.Theorem86.sub_eq_self_of_isFinitaryProjection


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **Theorem 8.6's range characterization, in full.** `sub f = f ↔ f` is a finitary projection. -/
theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ IsFinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩

end DomainTheory.Neighborhood
