/-ai
If every member of a finite set of natural numbers lies in some stage of an ascending chain, then the whole finite set is contained in a single stage.

Induct on the finite set. The empty set is contained in stage zero. After inserting an element, the inductive hypothesis covers the remainder by one stage and the hypothesis covers the new element by another. Monotonicity of the chain places both inside the stage at the maximum of those two indices.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.chain_mono

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

theorem exists_index_of_finset (xs : ℕ → Pomega)
    (hmono : ∀ n, xs n ⊆ xs (n + 1))
    (s : Finset ℕ) (h : ∀ k ∈ s, ∃ n, k ∈ xs n) :
    ∃ N, (s : Set ℕ) ⊆ xs N := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert i t hit ih =>
    obtain ⟨N, hN⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self _ _)
    refine ⟨max N Ni, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · exact chain_mono xs hmono Ni (max N Ni) (le_max_right _ _) hNi
    · exact chain_mono xs hmono N (max N Ni) (le_max_left _ _) (hN hj)

end DomainTheory.DataTypesAsLattices
