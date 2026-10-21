/-ai
The four-fold tensor of a, b, c, and d, applied to u, equals the four-way sequence of the applications of a, b, c, and d to the applications of u at the numerals 0, 1, 2, and 3.

This is the beta law for the graph of that body, using Scott continuity of the body.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem tensor4_app (a b c d u : Pomega) :
    funOf (tensor4 a b c d) u =
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3))) :=
  beta (tensor4_map_isScottContinuous a b c d) u

end DomainTheory.DataTypesAsLattices
