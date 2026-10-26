module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.7), remaining cases.** -/
theorem eq_2_7_pos (x y z : Pomega) (h0 : 0 ∉ z) (hne : z ≠ botElem) :
    condSet z x y = y := by
  have hpos : ∃ t, t + 1 ∈ z := by
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have : k ≠ 0 := fun h => h0 (h ▸ hk)
    exact ⟨k - 1, by
      have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero this).symm
      rwa [← this]⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨hny, _⟩
    · exact (h0 hz).elim
    · exact hny
  · intro hny
    exact Or.inr ⟨hny, hpos⟩

end DomainTheory.DataTypesAsLattices
