module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_of_pos_not_zero {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = y := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = y := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
      · exact (h0 hz).elim
      · exact hy
    · intro hy
      exact Or.inr ⟨hy, hp⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
    · exact (h0 hz).elim
    · exact hy
  · intro hy
    exact Or.inr ⟨hy, hp⟩

end DomainTheory.DataTypesAsLattices
