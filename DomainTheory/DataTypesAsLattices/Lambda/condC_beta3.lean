
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condC_beta3 (x y z : Pomega) :
    funOf (funOf (funOf condC x) y) z = condSet z x y := by
  rw [condC_beta2]
  exact beta (condSet_isScottContinuous_left x y) z

end DomainTheory.DataTypesAsLattices
