module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_z
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarStep_app2 (s u z : Pomega) :
    funOf (funOf (dollarStep s) u) z = dollarStepBody s u z := by
  rw [dollarStep_app]
  exact beta (dollarStepBody_isScottContinuous_z s u) z

end DomainTheory.DataTypesAsLattices
