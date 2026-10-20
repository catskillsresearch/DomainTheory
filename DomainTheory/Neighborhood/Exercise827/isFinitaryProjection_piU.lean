/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.isProjection_piU
import DomainTheory.Neighborhood.Exercise827.isFinitary_piU_of_isFinitary_piD
import DomainTheory.Neighborhood.Exercise827.isFinitaryProjection_piD


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27, in full: for `d` a polymorphic type, `Π(d)` is a type.** (In fact for *any*
`d` at all — see `isFinitaryProjection_piD`.) This is the exercise's own statement, the last exercise
in the book, closed. -/
theorem isFinitaryProjection_piU (d : ApproximableMap U U) : IsFinitaryProjection (piU d) :=
  ⟨isProjection_piU d, isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD d).2⟩

end DomainTheory.Neighborhood
