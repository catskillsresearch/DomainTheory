/-ai
The doubly strict conditional is Scott continuous in its middle argument.

The outer conditional is Scott continuous in its middle argument, and the inner conditional that supplies that argument is Scott continuous in its middle argument, so the composite is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z w (condSet z topElem y))
    (g := fun x => condSet z x topElem)
    (condSet_isScottContinuous_mid z (condSet z topElem y))
    (condSet_isScottContinuous_mid z topElem)

end DomainTheory.DataTypesAsLattices
