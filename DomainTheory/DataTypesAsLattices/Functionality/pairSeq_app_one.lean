
module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem pairSeq_app_one (x y : Pomega) : funOf (pairSeq x y) (ofNat 1) = y :=
  seq2.one x y

end DomainTheory.DataTypesAsLattices
