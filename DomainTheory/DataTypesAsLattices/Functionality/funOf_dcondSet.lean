module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_condSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem funOf_dcondSet (z x y w : Pomega) :
    funOf (dcondSet z x y) w = dcondSet z (funOf x w) (funOf y w) := by
  simp only [dcondSet]
  rw [funOf_condSet, funOf_condSet, funOf_condSet, funOf_top]

end DomainTheory.DataTypesAsLattices
