
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_i

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (β) for continuous `τ`.** `(λ x. τ)(y) = τ[y/x]`. -/
theorem beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2_i hτ]

end DomainTheory.DataTypesAsLattices
