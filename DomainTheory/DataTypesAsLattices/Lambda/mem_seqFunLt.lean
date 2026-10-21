/-ai
A number lies in the strict stage of a revaluation at bound n if and only if some index belonging to the argument is strictly below n and the number lies in the application of the functional to the numeral of that index.

Each direction unpacks the bounded double union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











































theorem mem_seqFunLt {u x : Pomega} {n k : ℕ} :
    k ∈ seqFunLt u x n ↔ ∃ i ∈ x, i < n ∧ k ∈ funOf u (ofNat i) := by
  constructor
  · intro hk
    obtain ⟨i, hi, hrest⟩ := Set.mem_iUnion₂.mp hk
    obtain ⟨hlt, hki⟩ := Set.mem_iUnion.mp hrest
    exact ⟨i, hi, hlt, hki⟩
  · intro ⟨i, hi, hlt, hki⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion.mpr ⟨hlt, hki⟩⟩

end DomainTheory.DataTypesAsLattices
