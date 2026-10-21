/-ai
The binary sequence of x and y, applied to the numeral 1, is y.

This is the application formula for the binary sequence at 1.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
