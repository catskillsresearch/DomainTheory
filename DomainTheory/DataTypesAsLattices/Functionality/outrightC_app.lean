/-ai
Application of the right projection to u is the conditional set of the first component of u, with bottom as the zero branch and the second component as the positive branch.

This is β-conversion, using Scott continuity of that conditional map.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outrightC_app (u : Pomega) :
    funOf outrightC u = condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)) :=
  beta outrightC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
