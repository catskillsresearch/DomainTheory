module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.lambR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.envR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.typed_apply_retract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem Htyped_typed (τ : LambTerm) :
    typed (Htyped τ) (arrowR envR lambR) :=
  typed_apply_retract
    (arrowR_isRetract envR_isRetract lambR_isRetract)

end DomainTheory.DataTypesAsLattices
