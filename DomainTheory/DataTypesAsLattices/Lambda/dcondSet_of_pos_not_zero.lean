/-ai
If the test omits 0 but contains a positive number, the doubly strict conditional returns its right argument.

The left inner conditional is ⊤ by its right branch. The right inner conditional equals the right argument, because its left branch is impossible and its right branch copies that argument. The outer conditional then copies the right argument in the same way.
ai-/
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
