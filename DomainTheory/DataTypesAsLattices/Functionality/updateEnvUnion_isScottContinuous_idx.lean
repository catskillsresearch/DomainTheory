
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem updateEnvUnion_isScottContinuous_idx (t x : Pomega) :
    IsScottContinuous (updateEnvUnion t x) :=
  minExtend_isScottContinuous (fun n => updateEnv t x n)

end DomainTheory.DataTypesAsLattices
