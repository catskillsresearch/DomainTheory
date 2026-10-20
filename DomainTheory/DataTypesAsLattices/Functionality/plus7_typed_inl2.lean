module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app_tag2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_typed_inl2 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a2) :
    typed (tagInj 2 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app_tag2, ← hx]

end DomainTheory.DataTypesAsLattices
