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
import DomainTheory.Neighborhood.Exercise813c.generatedBy_genPoint_box


namespace DomainTheory.Neighborhood








/-- Finite unions of `box`es (over any index type) are `GeneratedBy genPoint` — the same
`Finset.induction_on`/`Finset.set_biUnion_insert` idiom as `8.13(a)`'s `generatedBy_biUnion_affine`. -/
theorem generatedBy_genPoint_biUnion {β : Type*} (t : Finset β) (I : β → Finset ℕ)
    (f : β → ℕ → Bool) : GeneratedBy genPoint (⋃ b ∈ t, box (I b) (f b)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using generatedBy_genPoint_empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (generatedBy_genPoint_box _ _).union ih

end DomainTheory.Neighborhood
