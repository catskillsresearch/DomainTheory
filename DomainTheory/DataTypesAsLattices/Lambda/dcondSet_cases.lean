module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_cases (z : Pomega) :
    (0 ∈ z ∧ ¬ ∃ k, k + 1 ∈ z) ∨
      (0 ∉ z ∧ ∃ k, k + 1 ∈ z) ∨
        (0 ∈ z ∧ ∃ k, k + 1 ∈ z) ∨
          (0 ∉ z ∧ ¬ ∃ k, k + 1 ∈ z) := by
  by_cases h0 : 0 ∈ z
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inr (Or.inl ⟨h0, hp⟩))
    · exact Or.inl ⟨h0, hp⟩
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inl ⟨h0, hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h0, hp⟩))

end DomainTheory.DataTypesAsLattices
