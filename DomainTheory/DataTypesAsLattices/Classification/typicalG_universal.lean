
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_1

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3 / Theorem 6.1.** `𝔊` is the class of continuous
preimages of the typical open set `{x | 0 ∈ x}`. -/
theorem typicalG_universal (U : Set Pomega) :
    IsScottOpen U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalG} := by
  constructor
  · intro hU
    obtain ⟨f, hf, rfl⟩ := (theorem_6_1).2 U hU
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_1).1 f hf

end DomainTheory.DataTypesAsLattices
