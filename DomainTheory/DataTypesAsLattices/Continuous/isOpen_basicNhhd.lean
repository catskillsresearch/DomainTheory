/-ai
Every basic neighbourhood is open in the positive topology.

The finite set coded by n is the underlying set of some finite set s, and transporting membership along that equality writes the basic neighbourhood as the intersection of the subbasic opens of the members of s. Each of those subbasic opens is open, so their finite intersection is open.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
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
