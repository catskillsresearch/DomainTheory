/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.ContinuousLattice.Specialization

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- **March 1972 correction.** The given topology `τ` is coarser than (or equal to) the Scott
topology: every set open in `τ` is Scott-open. Equivalently `Opens(τ) ⊆ Opens(Scott)`,
i.e. `scottTopologicalSpace ≤ τ` in mathlib's order on topologies. -/
def CoarserThanScottTopology (τ : TopologicalSpace D) : Prop :=
  scottTopologicalSpace ≤ τ

end DomainTheory.ContinuousLattice
