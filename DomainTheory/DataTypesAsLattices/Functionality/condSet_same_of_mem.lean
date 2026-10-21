/-ai
If some natural number k lies in z, then the conditional set of z with both branches equal to x equals x.

Membership extensionality. An element of the conditional lies in one of the two branches, hence in x. Conversely, an element of x is placed in the left branch when k is zero and in the right branch when k is a successor, using the membership of k in z.
ai-/
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
