/-ai
This file gathers and re-exports the specialization order, Scott continuity, the Scott topology, and preservation of directed suprema, as the common setting for Scott-continuous maps in Scott's sections 2.5 through 2.7.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup

@[expose] public section

/-!
# Scott-continuous maps (Scott 1972, §2.5–2.7)
-/

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


/-! ### Proposition 2.6 -/

/-! ### Proposition 2.7 -/
end DomainTheory.ContinuousLattice
