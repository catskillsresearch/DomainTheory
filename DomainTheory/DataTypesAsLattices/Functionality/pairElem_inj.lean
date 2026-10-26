
module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairElem.inj {x y x' y' : Pomega} (h : pairElem x y = pairElem x' y') :
    x = x' ∧ y = y' :=
  pairSeq_inj h

end DomainTheory.DataTypesAsLattices
