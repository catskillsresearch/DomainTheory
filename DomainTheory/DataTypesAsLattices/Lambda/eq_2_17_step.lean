module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.17), fundamental equation.** -/
theorem eq_2_17_step (x y : Pomega) :
    x ∩ y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (predSet x ∩ predSet y)) := by
  ext n
  constructor
  · intro ⟨hnx, hny⟩
    cases n with
    | zero =>
      exact Or.inl ⟨Or.inl ⟨rfl, hny⟩, hnx⟩
    | succ n =>
      refine Or.inr ⟨⟨n, ⟨hnx, hny⟩, rfl⟩, n, hnx⟩
  · intro hn
    rcases hn with ⟨hL, h0x⟩ | ⟨⟨k, hk, rfl⟩, _t, _ht⟩
    · rcases hL with ⟨hk0, h0y⟩ | ⟨hbot, _⟩
      · simp [ofNat] at hk0; subst hk0
        exact ⟨h0x, h0y⟩
      · simp [botElem] at hbot
    · exact ⟨hk.1, hk.2⟩

end DomainTheory.DataTypesAsLattices
