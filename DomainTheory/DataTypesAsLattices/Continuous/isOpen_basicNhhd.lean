module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem isOpen_basicNhhd (n : ℕ) : IsOpen (basicNhhd n) := by
  obtain ⟨s, hs⟩ := (e_finite n).exists_finset_coe
  have h : basicNhhd n = ⋂ k ∈ s, memOpen k := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter₂.mpr ?_
      intro k hk
      have : k ∈ e n := by
        have : k ∈ (s : Set ℕ) := hk
        rwa [hs] at this
      exact hx this
    · intro hx k hk
      have : k ∈ s := by
        have : k ∈ e n := hk
        rwa [← hs] at this
      exact Set.mem_iInter₂.mp hx k this
  rw [h]
  exact isOpen_biInter_finset fun _ _ => isOpen_memOpen _

end DomainTheory.DataTypesAsLattices
