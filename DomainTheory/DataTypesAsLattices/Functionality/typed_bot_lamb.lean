
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_bot
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_bot_lamb : typed botElem lambR := by
  rw [eq_4_39]
  exact plusR_typed_bot _ _

end DomainTheory.DataTypesAsLattices
