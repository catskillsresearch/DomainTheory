module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_bot (x y : Pomega) : dcondSet botElem x y = botElem := by
  ext n
  simp [dcondSet, condSet, botElem]

end DomainTheory.DataTypesAsLattices
