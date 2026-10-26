module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.interC
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.17).** `x ∩ y = Y(λf λx λy. x ⊃ (y ⊃ 0, ⊥), f(x−1)(y−1)+1)(x)(y)`. -/
theorem eq_2_17 (x y : Pomega) :
    funOf (funOf interC x) y = x ∩ y := by
  have hmem : ∀ n x y, n ∈ funOf (funOf interC x) y ↔ n ∈ x ∩ y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y
      rw [interC.app]
      constructor
      · intro hn
        rcases hn with ⟨hL, h0x⟩ | ⟨⟨k, hk, rfl⟩, _t, _ht⟩
        · rcases hL with ⟨hk0, h0y⟩ | ⟨hbot, _⟩
          · simp [ofNat] at hk0; subst hk0
            exact ⟨h0x, h0y⟩
          · simp [botElem] at hbot
        · have hk' : k ∈ predSet x ∩ predSet y :=
            (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mp hk
          exact ⟨hk'.1, hk'.2⟩
      · intro ⟨hnx, hny⟩
        cases n with
        | zero => exact Or.inl ⟨Or.inl ⟨rfl, hny⟩, hnx⟩
        | succ k =>
          refine Or.inr ⟨⟨k, ?_, rfl⟩, k, hnx⟩
          exact (ih k (Nat.lt_succ_self k) (predSet x) (predSet y)).mpr ⟨hnx, hny⟩
  ext n
  exact hmem n x y

namespace eq_2_17

/-- **Scott 1976, (2.17), fundamental equation.** -/
theorem step (x y : Pomega) :
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

end eq_2_17

end DomainTheory.DataTypesAsLattices
