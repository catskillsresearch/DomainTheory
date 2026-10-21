/-ai
Scott 1976, (2.15). The union x ∪ y equals the conditional (λz. 0) ⊃ x, y.

The graph of the constant numeral 0 contains both 0 and 1. The left branch of the conditional therefore copies x, and the right branch copies y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.pair_zero_zero
public import DomainTheory.DataTypesAsLattices.Lambda.pair_one_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.15).** `x ∪ y = (λz. 0) ⊃ x, y`. -/
theorem eq_2_15 (x y : Pomega) :
    condSet (graph (fun _ => ofNat 0)) x y = x ∪ y := by
  have h0 : 0 ∈ graph (fun _ => ofNat 0) :=
    ⟨0, 0, pair_zero_zero.symm, by simp [ofNat]⟩
  have h1 : 1 ∈ graph (fun _ => ofNat 0) :=
    ⟨1, 0, pair_one_zero.symm, by simp [ofNat]⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hny, _⟩
    · exact Or.inl hnx
    · exact Or.inr hny
  · intro hn
    rcases hn with hnx | hny
    · exact Or.inl ⟨hnx, h0⟩
    · exact Or.inr ⟨hny, 0, h1⟩

end DomainTheory.DataTypesAsLattices
