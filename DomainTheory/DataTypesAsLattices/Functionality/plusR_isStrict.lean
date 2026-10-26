
module

public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_isStrict (a b : Pomega) : IsStrict (plusR a b) :=
  plusR_app_bot a b

end DomainTheory.DataTypesAsLattices
