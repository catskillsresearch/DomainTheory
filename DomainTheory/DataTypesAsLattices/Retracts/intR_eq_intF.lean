module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_eq_intF : intF intR = intR :=
  (theorem_1_4 intF_isScottContinuous).1

end DomainTheory.DataTypesAsLattices
