/-ai
Scott's Table 3 and Theorem 6.1 state that 𝔊 is the class of continuous preimages of the typical open set of x with 0 in x: a set U is Scott open if and only if U is the set of x whose image under some Scott-continuous f lies in that typical set.

If U is Scott open, the 𝔊 theorem supplies a Scott-continuous f for which U is the set of x with 0 in f(x), which is membership of f(x) in the typical set. Conversely, if U has that form, the first half of the 𝔊 theorem says that U is Scott open.
ai-/

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
