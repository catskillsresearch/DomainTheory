/-ai
The doubly strict conditional is Scott continuous in its right argument.

The outer conditional is Scott continuous in its right argument, and the inner conditional that supplies that argument is Scott continuous in its right argument, so the composite is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z (condSet z x topElem) w)
    (g := fun y => condSet z topElem y)
    (condSet_isScottContinuous_right z (condSet z x topElem))
    (condSet_isScottContinuous_right z topElem)

end DomainTheory.DataTypesAsLattices
