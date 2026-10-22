module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_same_of_mem {z x : Pomega} {k : ℕ} (hk : k ∈ z) :
    condSet z x x = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hnx, _⟩
    · exact hnx
    · exact hnx
  · intro hnx
    cases k with
    | zero => exact Or.inl ⟨hnx, hk⟩
    | succ t => exact Or.inr ⟨hnx, t, hk⟩

end DomainTheory.DataTypesAsLattices
