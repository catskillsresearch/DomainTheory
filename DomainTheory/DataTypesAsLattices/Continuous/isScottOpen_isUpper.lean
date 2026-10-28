module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem isScottOpen_isUpper {U : Set Pomega} (hU : IsScottOpen U)
    {x y : Pomega} (hx : x ∈ U) (hxy : x ⊆ y) : y ∈ U := by
  obtain ⟨B, rfl⟩ := hU
  obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨n, hn, subset_trans hxn hxy⟩

end DomainTheory.DataTypesAsLattices
