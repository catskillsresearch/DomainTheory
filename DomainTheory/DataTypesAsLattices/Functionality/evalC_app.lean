/-ai
Application of the evaluation combinator at u equals the application of the zeroth component of u to the first component of u.

This is the beta rule for the Scott continuity of evaluation, evaluated at u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.evalC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem evalC_app (u : Pomega) :
    funOf evalC u = funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)) :=
  beta evalC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
