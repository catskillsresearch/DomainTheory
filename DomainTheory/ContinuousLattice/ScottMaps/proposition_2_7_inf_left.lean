/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import DomainTheory.ContinuousLattice.ScottMaps.Basic
import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
import DomainTheory.ContinuousLattice.ScottMaps.meet_preservesDirectedSup


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']




/-- **Scott 1972, Proposition 2.7 (meet, separate).** On a continuous lattice, `x ↦ x ⊓ y`
and `y ↦ x ⊓ y` are Scott-continuous; Scott's full 2.7 also covers joint continuity on the
product via Proposition 2.6. -/
theorem proposition_2_7_inf_left (hD : IsContinuousLattice D) (y : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun x => x ⊓ y) :=
  continuous_of_preservesDirectedSup <| by
    intro S' hS' hSdir'
    rw [show (fun x => x ⊓ y) = fun z => y ⊓ z from funext fun x => inf_comm x y]
    have h := meet_preservesDirectedSup y hD
    exact h (S := S') hS' hSdir'

end DomainTheory.ContinuousLattice
