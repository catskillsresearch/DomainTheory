module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
