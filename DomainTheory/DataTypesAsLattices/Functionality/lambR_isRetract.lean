/-ai
Scott 1976, Theorem 4.6 applied to (4.39). The lambda retract is a retract.

Theorem 4.6 is applied to the Scott continuity of lambF and to the fact that a retract a is sent to the sum of the integer retract with the function space of a with itself, which is a retract. The retract component of that result is the claim.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 4.6 applied to (4.39).** -/
theorem lambR_isRetract : IsRetract lambR :=
  (theorem_4_6 lambF_isScottContinuous (fun _a ha =>
    plusR_isRetract intR_isRetract (arrowR_isRetract ha ha))).2

end DomainTheory.DataTypesAsLattices
