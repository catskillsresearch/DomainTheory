module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_ofNat_zero (x y : Pomega) : dcondSet (ofNat 0) x y = x := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

end DomainTheory.DataTypesAsLattices
