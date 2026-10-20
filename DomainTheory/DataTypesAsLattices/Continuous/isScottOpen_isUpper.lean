module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace






/-- Open sets are upper sets: if `x ∈ U` and `x ⊆ y` then `y ∈ U`. -/
theorem isScottOpen_isUpper {U : Set Pomega} (hU : IsScottOpen U)
    {x y : Pomega} (hx : x ∈ U) (hxy : x ⊆ y) : y ∈ U := by
  obtain ⟨B, rfl⟩ := hU
  obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨n, hn, subset_trans hxn hxy⟩

end DomainTheory.DataTypesAsLattices
