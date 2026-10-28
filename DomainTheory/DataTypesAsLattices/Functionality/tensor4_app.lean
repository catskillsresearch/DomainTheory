
module

public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
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
