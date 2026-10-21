/-ai
Application of a seven-way sum to u equals the body of that sum at u.

This is β-conversion, since the body is Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_app (a0 a1 a2 a3 a4 a5 a6 u : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u =
      plus7Body a0 a1 a2 a3 a4 a5 a6 u :=
  beta (plus7_map_isScottContinuous a0 a1 a2 a3 a4 a5 a6) u

end DomainTheory.DataTypesAsLattices
