/-ai
The operator HF fixes the raw least fixed point.

This is the fixed-point half of the fixed-point theorem, applied to continuity of HF.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.HF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hfun_fixed : HF Hfun = Hfun :=
  (theorem_1_4 HF_isScottContinuous).1

end DomainTheory.DataTypesAsLattices
