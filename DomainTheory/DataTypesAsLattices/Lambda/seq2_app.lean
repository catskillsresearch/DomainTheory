/-ai
The two-element sequence of two sets, applied to an argument, equals the conditional that returns the first set on a zero argument and otherwise the conditional of the predecessor that returns the second set or the bottom element.

The beta law applies, using continuity of that body.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem seq2_app (x y z : Pomega) :
    funOf (seq2 x y) z = condSet z x (condSet (predSet z) y botElem) :=
  beta (seq2_body_isScottContinuous x y) z

end DomainTheory.DataTypesAsLattices
