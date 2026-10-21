/-ai
The combinator H is typed by the arrow from the expression retract to the arrow from the environment retract to the lambda retract.

Apply the typing lemma for a retract to the arrow retract built from the expression, environment, and lambda retracts.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.lambR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.expR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.envR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.typed_apply_retract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem Hcomb_typed :
    typed Hcomb (arrowR expR (arrowR envR lambR)) :=
  typed_apply_retract
    (arrowR_isRetract expR_isRetract
      (arrowR_isRetract envR_isRetract lambR_isRetract))

end DomainTheory.DataTypesAsLattices
