/-ai
Application of the sum of a and b to u is the double conditional of the first component of u, with the sequence pair of zero and the application of a to the second component as the zero branch, and the sequence pair of one and the application of b to the second component as the positive branch.

This is β-conversion, since that map is Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_app (a b u : Pomega) :
    funOf (plusR a b) u =
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) :=
  beta (plusR_map_isScottContinuous a b) u

end DomainTheory.DataTypesAsLattices
