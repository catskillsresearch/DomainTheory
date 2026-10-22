/-ai
If f(x) is either ⊥ or ⊤, then the packing of f and g at x equals ⊤ + 1 if and only if f(x) is ⊥ and g(x) is ⊤.

Suppose the packing equals ⊤ + 1. Zero lies outside ⊤ + 1, so zero lies outside the packing and therefore outside f(x). The case f(x) = ⊤ is then impossible, and f(x) is ⊥. For each n the number n + 1 lies in the packing, and it cannot arise from the zero clause, so n belongs to g(x) and g(x) is ⊤. Conversely, if f(x) is ⊥ and g(x) is ⊤, the zero clause of the packing is empty, every successor member is a member of ⊤ + 1, and every member of ⊤ + 1 arises as such a successor.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.zero_not_mem_succSet_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem fcapGdeltaPack_eq {f g : Pomega → Pomega} {x : Pomega}
    (hfval : f x = botElem ∨ f x = topElem) :
    fcapGdeltaPack f g x = succSet topElem ↔ f x = botElem ∧ g x = topElem := by
  constructor
  · intro h
    constructor
    · have h0 : 0 ∉ fcapGdeltaPack f g x := by
        rw [h]; exact zero_not_mem_succSet_top
      have : 0 ∉ f x := fun hf0 => h0 (Or.inl ⟨rfl, hf0⟩)
      rcases hfval with hf | hf
      · exact hf
      · exact (this (by rw [hf]; exact Set.mem_univ 0)).elim
    · ext n
      constructor
      · intro _; trivial
      · intro _
        have : n + 1 ∈ fcapGdeltaPack f g x := by
          rw [h]; exact ⟨n, Set.mem_univ n, rfl⟩
        rcases this with ⟨hk0, _⟩ | ⟨m, hm, hmn⟩
        · exact (Nat.succ_ne_zero n (by simp [hk0])).elim
        · exact Nat.succ_injective hm ▸ hmn
  · intro ⟨hf, hg⟩
    ext k
    constructor
    · intro hk
      rcases hk with ⟨_, h0⟩ | ⟨n, hk, hn⟩
      · rw [hf] at h0; exact ((mem_botElem 0).mp h0).elim
      · exact ⟨n, Set.mem_univ n, hk⟩
    · intro hk
      obtain ⟨n, _, rfl⟩ := hk
      refine Or.inr ⟨n, rfl, ?_⟩
      rw [hg]; exact Set.mem_univ n

end DomainTheory.DataTypesAsLattices
