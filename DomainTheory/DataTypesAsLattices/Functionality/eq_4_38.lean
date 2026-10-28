module

public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.treeF_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_38 : treeR = plusR botElem (tensorR treeR treeR) := by
  have hY : treeR = fix treeF := theorem_2_5 treeF_isScottContinuous
  have hfix : treeF treeR = treeR := by
    rw [hY]
    exact (theorem_1_4 treeF_isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
