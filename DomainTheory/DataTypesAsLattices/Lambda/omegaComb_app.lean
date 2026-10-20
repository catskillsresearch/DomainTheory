module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























theorem omegaComb_app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) diagApp_isScottContinuous) x

end DomainTheory.DataTypesAsLattices
