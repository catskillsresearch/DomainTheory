module

public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.evalC_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem evalC_app (u : Pomega) :
    funOf evalC u = funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)) :=
  beta evalC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
