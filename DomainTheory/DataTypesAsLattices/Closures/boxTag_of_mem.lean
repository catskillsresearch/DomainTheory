module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTag_of_mem {x : Pomega} {m : ℕ} (hm : m ∈ x) (i : ℕ) :
    boxTag i x = ofNat i := by
  ext n
  simp only [boxTag, condSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    cases m with
    | zero => exact Or.inl ⟨hn, hm⟩
    | succ k => exact Or.inr ⟨hn, k, hm⟩

end DomainTheory.DataTypesAsLattices
