module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.exists_basicNhhd_subset_of_generateOpen
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

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
