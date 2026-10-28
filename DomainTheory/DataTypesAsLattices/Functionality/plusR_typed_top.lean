
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem plusR_typed_top (a b : Pomega) : typed topElem (plusR a b) :=
  (plusR_app.top a b).symm

end DomainTheory.DataTypesAsLattices
