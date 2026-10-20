/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Exercise812c.Basic
import DomainTheory.Neighborhood.Exercise812c.V_mem_nonempty


namespace DomainTheory.Neighborhood

open NeighborhoodSystem







theorem V_noMinimal : V.NoMinimal := by
  intro X hX
  obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := V_no_minimal hX
  exact ⟨Y, Z, hY, hZ, V_mem_nonempty hY, V_mem_nonempty hZ, hYZinter, hYZunion⟩

end DomainTheory.Neighborhood
