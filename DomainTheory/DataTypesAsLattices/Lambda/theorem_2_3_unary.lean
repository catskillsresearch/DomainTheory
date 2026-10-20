module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 2.3, unary case.** -/
theorem theorem_2_3_unary {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∃ u, ∀ x, funOf u x = f x :=
  ⟨graph f, fun x => by rw [theorem_1_2_i hf]⟩

end DomainTheory.DataTypesAsLattices
