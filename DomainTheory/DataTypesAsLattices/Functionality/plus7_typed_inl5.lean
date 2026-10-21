/-ai
If x has the type of the sixth summand, then the injection of x at tag 5 has the type of the seven-way sum.

Rewrite the typing equation by the application clause for tag 5, and substitute the typing equation of x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app_tag5

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_typed_inl5 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a5) :
    typed (tagInj 5 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag5, ← hx]

end DomainTheory.DataTypesAsLattices
