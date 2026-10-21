/-ai
The predecessor combinator applied to a set equals the predecessor of that set.

The beta law applies, using Scott continuity of the predecessor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem predC_app (x : Pomega) : funOf predC x = predSet x :=
  beta predSet_isScottContinuous x

end DomainTheory.DataTypesAsLattices
