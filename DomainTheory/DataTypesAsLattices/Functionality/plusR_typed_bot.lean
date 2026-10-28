
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem plusR_typed_bot (a b : Pomega) : typed botElem (plusR a b) := by
  rw [typed, plusR_app.app, funOf.bot, dcondSet.bot]

end DomainTheory.DataTypesAsLattices
