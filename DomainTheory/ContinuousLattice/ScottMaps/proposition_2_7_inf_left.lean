/-ai
On a continuous lattice, meet on the left with a fixed element is Scott-continuous. This is the separate meet clause of Scott's Proposition 2.7; the joint statement on the product is Proposition 2.6.

Continuity follows from preservation of directed suprema. Commuting the two arguments of the meet reduces that preservation to preservation by meet with the same fixed element on the right.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.meet_preservesDirectedSup

@[expose] public section


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
