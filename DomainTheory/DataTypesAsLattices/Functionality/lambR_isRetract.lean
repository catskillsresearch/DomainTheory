
module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem lambR_isRetract : Retract lambR :=
  (theorem_4_6 lambF_isScottContinuous (fun _a ha =>
    plusR_isRetract intR.isRetract (arrowR.isRetract ha ha))).2

end DomainTheory.DataTypesAsLattices
