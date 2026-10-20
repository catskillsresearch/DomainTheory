module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interStep_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_unfold : interC = interStep interC :=
  (theorem_1_4 interStep_isScottContinuous).1.symm

end DomainTheory.DataTypesAsLattices
