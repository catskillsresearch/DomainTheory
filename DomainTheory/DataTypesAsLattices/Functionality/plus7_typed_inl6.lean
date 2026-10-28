
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem plus7_typed_inl6 {a0 a1 a2 a3 a4 a5 a6 x : Pomega} (hx : typed x a6) :
    typed (tagInj 6 x) (plus7 a0 a1 a2 a3 a4 a5 a6) := by
  rw [typed, plus7_app.tag6, ← hx]

end DomainTheory.DataTypesAsLattices
