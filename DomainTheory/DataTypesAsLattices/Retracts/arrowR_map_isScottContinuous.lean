/-ai
The map sending u to the composition of b after u after a is Scott continuous.

Theorem 1.3 substitutes left composition with b, which is Scott continuous, into right composition with a, which is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.comp_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Retracts.comp_right_const

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem arrowR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u => comp b (comp u a)) :=
  theorem_1_3 (comp_isScottContinuous_right b) (comp_right_const a)

end DomainTheory.DataTypesAsLattices
