/-ai
A sum is strict.

Strictness is the equation that the sum sends bottom to bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_isStrict (a b : Pomega) : IsStrict (plusR a b) :=
  plusR_app_bot a b

end DomainTheory.DataTypesAsLattices
