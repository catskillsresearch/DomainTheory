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
import DomainTheory.Neighborhood.Exercise813c.isClopen_genPoint


namespace DomainTheory.Neighborhood





/-- **Easy direction**: everything `GeneratedBy genPoint` is clopen. -/
theorem generatedBy_genPoint_isClopen {Y : Set (ℕ → Bool)} (h : GeneratedBy genPoint Y) :
    IsClopen Y := by
  induction h with
  | of i => exact isClopen_genPoint i
  | univ => exact isClopen_univ
  | inter _ _ ih1 ih2 => exact ih1.inter ih2
  | union _ _ ih1 ih2 => exact ih1.union ih2
  | compl _ ih => exact ih.compl

end DomainTheory.Neighborhood
