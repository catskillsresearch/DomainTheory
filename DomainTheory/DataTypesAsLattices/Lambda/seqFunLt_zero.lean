module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.mem_seqFunLt

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











































theorem seqFunLt_zero (u z : Pomega) : seqFunLt u z 0 = botElem := by
  ext k
  simp [mem_seqFunLt, botElem]

end DomainTheory.DataTypesAsLattices
