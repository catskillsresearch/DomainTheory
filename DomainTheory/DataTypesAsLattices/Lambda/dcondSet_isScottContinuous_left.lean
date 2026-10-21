/-ai
The doubly strict conditional is Scott continuous in its test.

It is the McCarthy conditional of the test, of the conditional of the test on the left argument and ⊤, and of the conditional of the test on ⊤ and the right argument. The McCarthy conditional is Scott continuous in each argument, the test is copied by the identity, and each inner conditional is Scott continuous in the test.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => dcondSet z x y) :=
  theorem_1_3_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous
    (condSet_isScottContinuous_left x topElem)
    (condSet_isScottContinuous_left topElem y)

end DomainTheory.DataTypesAsLattices
