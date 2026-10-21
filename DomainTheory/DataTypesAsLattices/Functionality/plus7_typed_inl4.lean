/-ai
If x has the type of the fifth summand, then the injection of x at tag 4 has the type of the seven-way sum.

Rewrite the typing equation by the application clause for tag 4, and substitute the typing equation of x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app_tag4

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_typed_inl4 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a4) :
    typed (tagInj 4 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag4, ← hx]

end DomainTheory.DataTypesAsLattices
