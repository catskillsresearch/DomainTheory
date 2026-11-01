module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem funOf_botElem (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

end DomainTheory.DataTypesAsLattices
