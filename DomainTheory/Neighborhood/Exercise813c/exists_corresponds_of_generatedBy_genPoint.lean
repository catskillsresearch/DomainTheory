/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813b
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import DomainTheory.Neighborhood.Exercise813c.Basic


namespace DomainTheory.Neighborhood



















theorem exists_corresponds_of_generatedBy_genPoint {Y : Set (ℕ → Bool)}
    (hY : GeneratedBy genPoint Y) : ∃ X, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet'.mp hY
  exact ⟨evalSet φ, φ, rfl, hφ⟩

end DomainTheory.Neighborhood
