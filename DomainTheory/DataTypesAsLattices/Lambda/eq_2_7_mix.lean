/-ai
If the test contains 0 and is not the numeral 0, the McCarthy conditional equals the union of its two branches.

Some positive number then belongs to the test, since otherwise the test would equal {0}. Both branches are therefore available, and membership splits as the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_7_mix (x y z : Pomega) (h0 : 0 ∈ z) (hne : z ≠ ofNat 0) :
    condSet z x y = x ∪ y := by
  have hpos : ∃ t, t + 1 ∈ z := by
    by_contra h
    apply hne
    ext k
    constructor
    · intro hk
      have : k = 0 := by
        by_contra hk0
        exact h ⟨k - 1, by
          have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero hk0).symm
          rwa [← this]⟩
      simp [this, ofNat]
    · intro hk
      simp [ofNat] at hk
      subst hk
      exact h0
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hny, _⟩
    · exact Or.inl hnx
    · exact Or.inr hny
  · intro hn
    rcases hn with hnx | hny
    · exact Or.inl ⟨hnx, h0⟩
    · exact Or.inr ⟨hny, hpos⟩

end DomainTheory.DataTypesAsLattices
