/-ai
Every nonempty set of natural numbers has a least member.

Strong induction shows that if n belongs to the set, then some k at most n belongs to the set and no smaller index does: either n itself is such a least member, or some smaller index belongs and the inductive hypothesis applies. The nonempty hypothesis supplies an n, and that claim yields the least member.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































lemma exists_least_mem {a : Pomega} (hex : ∃ k, k ∈ a) :
    ∃ k, k ∈ a ∧ ∀ i < k, i ∉ a := by
  have : ∀ n, n ∈ a → ∃ k ≤ n, k ∈ a ∧ ∀ i < k, i ∉ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Classical.em (∀ i < n, i ∉ a) with hmin | hmin
      · exact ⟨n, le_rfl, hn, hmin⟩
      · obtain ⟨i, hi⟩ := not_forall.mp hmin
        have hi' : i < n := (Classical.not_imp.mp hi).1
        have hia : i ∈ a := not_not.mp (Classical.not_imp.mp hi).2
        obtain ⟨k, hki, hk, hall⟩ := ih i hi' hia
        exact ⟨k, hki.trans hi'.le, hk, hall⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, _, hk, hall⟩ := this n hn
  exact ⟨k, hk, hall⟩

end DomainTheory.DataTypesAsLattices
