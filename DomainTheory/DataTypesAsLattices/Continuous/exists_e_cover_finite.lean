module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- If each element of a finite set is realized at some `e n ⊆ x`, the
bitwise-OR of those codes realizes the whole finite set (using monotonicity). -/
theorem exists_e_cover_finite {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (s : Finset ℕ)
    (h : ∀ k ∈ s, ∃ n, e n ⊆ x ∧ k ∈ f (e n)) :
    ∃ N, e N ⊆ x ∧ (s : Set ℕ) ⊆ f (e N) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp [e_zero], by simp⟩
  | insert k s hks ih =>
    obtain ⟨N, hN, hs⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨n, hn, hk⟩ := h k (Finset.mem_insert_self _ _)
    refine ⟨n ||| N, e_or_of_subset hn hN, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · have : e n ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_left
      exact IsScottContinuous.monotone hf this hk
    · have : e N ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_right
      exact IsScottContinuous.monotone hf this (hs hj)

end DomainTheory.DataTypesAsLattices
