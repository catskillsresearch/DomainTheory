/-ai
Bottom is typed by bottom.

Unfold the typing as the equality of bottom with the application of bottom to itself, then rewrite by the application law for bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_bot_botElem : typed botElem botElem := by
  change botElem = funOf botElem botElem
  rw [funOf_bot]

end DomainTheory.DataTypesAsLattices
