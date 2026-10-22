
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_typed_bot (a b : Pomega) : typed botElem (plusR a b) := by
  rw [typed, plusR_app, funOf_bot, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
