module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_condSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem funOf_dcondSet (z x y w : Pomega) :
    funOf (dcondSet z x y) w = dcondSet z (funOf x w) (funOf y w) := by
  simp only [dcondSet]
  rw [funOf_condSet, funOf_condSet, funOf_condSet, funOf_top]

end DomainTheory.DataTypesAsLattices
