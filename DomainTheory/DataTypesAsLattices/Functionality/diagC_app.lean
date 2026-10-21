/-ai
Application of the diagonal combinator at u equals the pair sequence of u with itself.

This is the beta rule for diagonal continuity of the pair sequence, from its left and right continuities, evaluated at u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_on_diag
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem diagC_app (u : Pomega) : funOf diagC u = pairSeq u u :=
  beta (continuous_on_diag
    pairSeq_isScottContinuous_left pairSeq_isScottContinuous_right) u

end DomainTheory.DataTypesAsLattices
