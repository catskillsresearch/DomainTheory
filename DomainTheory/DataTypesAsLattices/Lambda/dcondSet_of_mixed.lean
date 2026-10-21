/-ai
If the test contains both 0 and some positive number, the doubly strict conditional is ⊤.

The left inner conditional is ⊤ because its right branch contains every number, and the right inner conditional is ⊤ because its left branch contains every number. The outer conditional is then ⊤ by its left branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_of_mixed {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = topElem := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro _; exact Set.mem_univ n
  · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩

end DomainTheory.DataTypesAsLattices
