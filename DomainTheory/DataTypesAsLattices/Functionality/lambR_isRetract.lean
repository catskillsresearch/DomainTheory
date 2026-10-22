
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.6 applied to (4.39).** -/
theorem lambR_isRetract : Retract lambR :=
  (theorem_4_6 lambF_isScottContinuous (fun _a ha =>
    plusR_isRetract intR_isRetract (arrowR_isRetract ha ha))).2

end DomainTheory.DataTypesAsLattices
