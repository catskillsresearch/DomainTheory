/-ai
Element pairing is injective in both arguments.

This is injectivity of sequence pairing applied to the same equality.
ai-/

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
