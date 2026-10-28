
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem typed_bot_botElem : typed botElem botElem := by
  change botElem = funOf botElem botElem
  rw [funOf.bot]

end DomainTheory.DataTypesAsLattices
