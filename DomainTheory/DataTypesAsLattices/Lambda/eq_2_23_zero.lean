module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_23_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x :=
  seq2.zero x y

end DomainTheory.DataTypesAsLattices
