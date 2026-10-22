module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_bot (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

end DomainTheory.DataTypesAsLattices
