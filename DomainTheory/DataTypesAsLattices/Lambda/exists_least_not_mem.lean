/-ai
If some natural number lies outside a set, then there is a least such number, and every smaller index lies in the set.

Strong induction shows that if n lies outside the set, then some k at most n lies outside and every smaller index lies in the set: either n itself is least, or some smaller index lies outside and the inductive hypothesis applies. The hypothesis supplies an n, and that claim yields the least missing number.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


lemma exists_least_not_mem {a : Pomega} (hex : ∃ k, k ∉ a) :
    ∃ k, k ∉ a ∧ ∀ i < k, i ∈ a := by
  have : ∀ n, n ∉ a → ∃ k ≤ n, k ∉ a ∧ ∀ i < k, i ∈ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Classical.em (∀ i < n, i ∈ a) with hmin | hmin
      · exact ⟨n, le_rfl, hn, hmin⟩
      · obtain ⟨i, hi⟩ := not_forall.mp hmin
        have hi' : i < n := (Classical.not_imp.mp hi).1
        have hia : i ∉ a := (Classical.not_imp.mp hi).2
        obtain ⟨k, hki, hk, hall⟩ := ih i hi' hia
        exact ⟨k, hki.trans hi'.le, hk, hall⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, _, hk, hall⟩ := this n hn
  exact ⟨k, hk, hall⟩

end DomainTheory.DataTypesAsLattices
