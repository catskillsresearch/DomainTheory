/-ai
Applying the term shift of u to t equals applying u to the successor of t.

This is the β-law for that body, which is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.termShift_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termShift_app (u t : Pomega) :
    funOf (termShift u) t = funOf u (succSet t) :=
  beta (termShift_isScottContinuous u) t

end DomainTheory.DataTypesAsLattices
