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
import DomainTheory.ContinuousLattice.ScottMaps.continuous_preservesDirectedSup


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


/-- **Scott 1972, Proposition 2.5.** Scott continuity ↔ preservation of directed suprema. -/
theorem proposition_2_5 (f : D → D') :
    (@Continuous D D' scottTopologicalSpace scottTopologicalSpace f) ↔
      PreservesDirectedSup f :=
  ⟨continuous_preservesDirectedSup, fun hf => continuous_of_preservesDirectedSup hf⟩

end DomainTheory.ContinuousLattice
