
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Ycomb_app (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) :=
  beta (theorem_1_3 diagApp_isScottContinuous omegaComb_isScottContinuous) u

end DomainTheory.DataTypesAsLattices
