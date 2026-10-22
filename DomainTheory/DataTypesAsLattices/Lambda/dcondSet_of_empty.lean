module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_of_empty {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = botElem := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
    · exact (h0 hz).elim
    · exact (hp ht).elim
  · intro hn
    simp [botElem] at hn

end DomainTheory.DataTypesAsLattices
