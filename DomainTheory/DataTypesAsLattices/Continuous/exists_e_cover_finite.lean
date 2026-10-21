/-ai
If f is Scott continuous and every member of a finite set s of natural numbers lies in f of some finite subset of x, then one finite code N has its finite set contained in x and the whole of s contained in f of that finite set.

The argument is an induction on s. The empty set is realized by the code 0. When k is inserted, the inductive code N is combined by bitwise or with a code n that realizes k. Each of those finite sets is contained in the finite set of the combined code, so monotonicity of the Scott continuous map f puts both k and the rest of s into f of the combined finite set.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_monotone

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
      exact isScottContinuous_monotone hf this hk
    · have : e N ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_right
      exact isScottContinuous_monotone hf this (hs hj)

end DomainTheory.DataTypesAsLattices
