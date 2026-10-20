/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise813a.Basic
import DomainTheory.Neighborhood.Exercise813a.generatedBy_biUnion_affine


namespace DomainTheory.Neighborhood

open NeighborhoodSystem











theorem generatedBy_levelSet (k m : ℕ) : GeneratedBy generator (levelSet k m) := by
  rw [levelSet_eq_biUnion]
  exact generatedBy_biUnion_affine k _ fun ℓ hℓ => (Finset.mem_filter.mp hℓ).1 |> Finset.mem_range.mp

end DomainTheory.Neighborhood
