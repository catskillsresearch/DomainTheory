module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.curryC
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.curry_body_isScottContinuous_y
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryC_app3 (u x y : Pomega) :
    funOf (funOf (funOf curryC u) x) y = funOf u (pairSeq x y) := by
  rw [curryC_app2]
  exact beta (curry_body_isScottContinuous_y u x) y

end DomainTheory.DataTypesAsLattices
