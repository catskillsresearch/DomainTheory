/-ai
Element pairing agrees with sequence pairing.

The two sides are definitionally equal.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairElem_eq_pairSeq (x y : Pomega) : pairElem x y = pairSeq x y := rfl

end DomainTheory.DataTypesAsLattices
