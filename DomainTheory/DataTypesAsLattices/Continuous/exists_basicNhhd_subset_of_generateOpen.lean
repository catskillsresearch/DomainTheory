module

public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd_more
@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- Every open neighbourhood of `x` contains a basic neighbourhood of `x`. -/
theorem exists_basicNhhd_subset_of_generateOpen {U : Set Pomega}
    (hU : GenerateOpen (Set.range memOpen) U) {x : Pomega} (hx : x ∈ U) :
    ∃ n, e n ⊆ x ∧ basicNhhd n ⊆ U := by
  induction hU generalizing x with
  | basic s hs =>
    obtain ⟨k, rfl⟩ := hs
    refine ⟨2 ^ k, ?_, ?_⟩
    · simpa [memOpen, e_pow2, Set.singleton_subset_iff] using hx
    · rw [← memOpen.eq_basicNhhd]
  | univ =>
    exact ⟨0, by simp [e_zero], by simp [basicNhhd.zero]⟩
  | inter _s _t _hs _ht ihs iht =>
    obtain ⟨n, hn, hnU⟩ := ihs hx.1
    obtain ⟨m, hm, hmU⟩ := iht hx.2
    refine ⟨n ||| m, e_or_of_subset hn hm, ?_⟩
    rw [← basicNhhd.inter]
    exact Set.inter_subset_inter hnU hmU
  | sUnion S _hS ih =>
    obtain ⟨V, hV, hxV⟩ := hx
    obtain ⟨n, hn, hnV⟩ := ih V hV hxV
    exact ⟨n, hn, hnV.trans (Set.subset_sUnion_of_mem hV)⟩

end DomainTheory.DataTypesAsLattices
