module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

namespace basicNhhd

/-- A basic neighbourhood is a finite intersection of subbasic opens. -/
theorem eq_iInter (n : ℕ) :
    basicNhhd n = ⋂ k ∈ e n, memOpen k := by
  ext x
  simp [basicNhhd, memOpen, Set.subset_def]

end basicNhhd

end DomainTheory.DataTypesAsLattices
