module

public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)
end DomainTheory.DataTypesAsLattices
