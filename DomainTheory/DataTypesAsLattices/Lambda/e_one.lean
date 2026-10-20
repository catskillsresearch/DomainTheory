module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem e_one : e 1 = ({0} : Pomega) := by
  simpa using e_pow2 0

end DomainTheory.DataTypesAsLattices
