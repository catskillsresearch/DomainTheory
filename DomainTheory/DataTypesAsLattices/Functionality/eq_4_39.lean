/-ai
Scott 1976, (4.39). The lambda retract equals the sum of the integer retract with the arrow of the lambda retract into itself.

Theorem 2.5, from Scott continuity of the lambda functor, identifies the lambda retract with the fixed point of that functor. Theorem 1.4 says the fixed point is fixed, so the functor returns the lambda retract. The reverse of that equality is the claim.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
theorem eq_4_39 : lambR = plusR intR (arrowR lambR lambR) := by
  have hY : lambR = fix lambF := theorem_2_5 lambF_isScottContinuous
  have hfix : lambF lambR = lambR := by
    rw [hY]
    exact (theorem_1_4 lambF_isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
