/-ai
Application of the left projection to u is the conditional set of the first component of u, with the second component as the zero branch and bottom as the positive branch.

This is β-conversion, using Scott continuity of that conditional map.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outleftC_app (u : Pomega) :
    funOf outleftC u = condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem :=
  beta outleftC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
