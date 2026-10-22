/-ai
A Scott open set is an upper set: if x lies in U and x is contained in y, then y lies in U.

Write U as a union of basic neighbourhoods. Membership of x selects a code whose finite set is contained in x. Transitivity of inclusion puts that finite set inside y, so y lies in the same basic neighbourhood.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
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
