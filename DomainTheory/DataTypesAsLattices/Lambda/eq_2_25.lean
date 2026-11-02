module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.sequences
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_25 (u x : Pomega) :
    funOf (funOf dollarC u) x = seqFun u x := by
  rw [dollarC.app]
  exact beta (seqFun.right_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
