module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem typed_bot_bot : typed botElem botElem := by
  change botElem = funOf botElem botElem
  rw [funOf_bot]

end DomainTheory.DataTypesAsLattices
