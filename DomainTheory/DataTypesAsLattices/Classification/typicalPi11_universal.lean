/-ai
Scott's Table 3 states that Π₁¹ is the class of continuous preimages of the set of u such that for every y there is a z with u(y)(z) equal to {0}.

In both directions the witness is copied unchanged: a continuous h exhibits U as a Π₁¹ set exactly when U is the preimage of the typical set under h.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace









































































































/-- **Scott 1976, Table 3.** `Π₁¹` is the class of continuous preimages of
`{u | ∀ y ∃ z. u(y)(z) = 0}`. -/
theorem typicalPi11_universal (U : Set Pomega) :
    IsPi11 U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalPi11} := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

end DomainTheory.DataTypesAsLattices
