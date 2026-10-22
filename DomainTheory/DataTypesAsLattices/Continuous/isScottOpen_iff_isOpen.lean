/-ai
In the sense of Scott 1976, §1, a set of elements of Pω is Scott open if and only if it is open in the positive information topology.

A Scott open set is a union of basic neighbourhoods, and each basic neighbourhood is open, so the union is open. If U is open, index it by those codes whose basic neighbourhood is contained in U. A point of U has, by the neighbourhood basis for a generated open, some basic neighbourhood contained in U, so it lies in that union. A point of the union lies in one such basic neighbourhood, hence in U.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.exists_basicNhhd_subset_of_generateOpen

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, §1.** Scott-open sets are exactly the opens of the
positive information topology. -/
theorem isScottOpen_iff_isOpen (U : Set Pomega) : IsScottOpen U ↔ IsOpen U := by
  constructor
  · intro ⟨B, hU⟩
    rw [hU]
    exact isOpen_biUnion fun n _ => isOpen_basicNhhd n
  · intro hU
    refine ⟨{n | basicNhhd n ⊆ U}, ?_⟩
    ext x
    constructor
    · intro hx
      have hgen : GenerateOpen (Set.range memOpen) U := hU
      obtain ⟨n, hn, hsub⟩ := exists_basicNhhd_subset_of_generateOpen hgen hx
      exact Set.mem_iUnion₂.mpr ⟨n, hsub, hn⟩
    · intro hx
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      exact hn hxn

end DomainTheory.DataTypesAsLattices
