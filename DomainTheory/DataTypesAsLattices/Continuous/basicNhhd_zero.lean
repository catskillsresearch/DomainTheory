module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem basicNhhd_zero : basicNhhd 0 = Set.univ := by
  ext x
  simp [basicNhhd, e_zero]

end DomainTheory.DataTypesAsLattices
