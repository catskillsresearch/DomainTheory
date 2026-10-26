module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.curryC
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.curry_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryC_app2 (u x : Pomega) :
    funOf (funOf curryC u) x = graph (fun y => funOf u (pairSeq x y)) := by
  rw [curryC_app]
  exact beta (curry_mid_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
