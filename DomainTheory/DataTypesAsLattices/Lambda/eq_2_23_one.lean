module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2.one x y

end DomainTheory.DataTypesAsLattices
