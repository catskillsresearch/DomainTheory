/-ai
For fixed t and x, the index-continuous environment update is Scott continuous in the index.

It is the minimal extension of the single-index updates, and that extension is Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem updateEnvUnion_isScottContinuous_idx (t x : Pomega) :
    IsScottContinuous (updateEnvUnion t x) :=
  minExtend_isScottContinuous (fun n => updateEnv t x n)

end DomainTheory.DataTypesAsLattices
