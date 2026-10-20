/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise820.Basic
import DomainTheory.Neighborhood.Exercise820.D_trianglelefteq_prod
import DomainTheory.Neighborhood.Exercise820.D_trianglelefteq_funSpace


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v






variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20.** For any domain `D`, `D ⊴ D×D` and `D ⊴ D→D` (unconditionally — no hypotheses
needed, unlike Exercise 8.19). See the module docstring for the discussion of computability and
multiplicity of projection pairs that Scott also asks about. -/
theorem exercise_8_20 : D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  ⟨D_trianglelefteq_prod D, D_trianglelefteq_funSpace D⟩

end DomainTheory.Neighborhood
