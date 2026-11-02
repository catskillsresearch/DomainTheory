module

public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
import Mathlib.Tactic.Bound.Init

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)
end DomainTheory.DataTypesAsLattices
