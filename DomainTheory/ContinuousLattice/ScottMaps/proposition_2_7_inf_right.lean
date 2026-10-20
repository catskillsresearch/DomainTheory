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




theorem proposition_2_7_inf_right (hD : IsContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) :=
  continuous_of_preservesDirectedSup (meet_preservesDirectedSup x hD)

end DomainTheory.ContinuousLattice
