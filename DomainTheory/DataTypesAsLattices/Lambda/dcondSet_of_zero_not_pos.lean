module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_of_zero_not_pos {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = x := by
  have hL : condSet z x topElem = x := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
      · exact hx
      · exact (hp ht).elim
    · intro hx
      exact Or.inl ⟨hx, h0⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
    · exact hx
    · exact (hp ht).elim
  · intro hx
    exact Or.inl ⟨hx, h0⟩

end DomainTheory.DataTypesAsLattices
