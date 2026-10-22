
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairElem_inj {x y x' y' : Pomega} (h : pairElem x y = pairElem x' y') :
    x = x' ∧ y = y' :=
  pairSeq_inj h

end DomainTheory.DataTypesAsLattices
