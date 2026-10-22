
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app_tag6

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_typed_inl6 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a6) :
    typed (tagInj 6 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag6, ← hx]

end DomainTheory.DataTypesAsLattices
