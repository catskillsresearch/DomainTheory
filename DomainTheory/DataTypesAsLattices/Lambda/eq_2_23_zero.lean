/-ai
Scott 1976, (2.23). The binary sequence of x and y, applied to the numeral 0, is x.

This is the application formula for the binary sequence at 0.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































/-- **Scott 1976, (2.23).** Projection of a binary sequence. -/
theorem eq_2_23_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x :=
  seq2_app_zero x y

end DomainTheory.DataTypesAsLattices
