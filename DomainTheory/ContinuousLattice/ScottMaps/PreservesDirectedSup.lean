module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

def PreservesDirectedSup (f : D → D') : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → f (sSup S) = sSup (f '' S)

end DomainTheory.ContinuousLattice
