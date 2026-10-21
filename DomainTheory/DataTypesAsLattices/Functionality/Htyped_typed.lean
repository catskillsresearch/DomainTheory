/-ai
The typed interpretation of a lambda term has type the arrow from the environment retract to the lambda retract.

Apply the typing lemma for a retract to the arrow retract built from the environment and lambda retracts.
ai-/
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
