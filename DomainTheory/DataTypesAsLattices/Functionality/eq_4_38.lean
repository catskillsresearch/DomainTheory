module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.treeF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























/-- **Scott 1976, (4.38).** `tree = nil ⊕ (tree ⊗ tree)`. -/
theorem eq_4_38 : treeR = plusR botElem (tensorR treeR treeR) := by
  have hY : treeR = fix treeF := theorem_2_5 treeF_isScottContinuous
  have hfix : treeF treeR = treeR := by
    rw [hY]
    exact (theorem_1_4 treeF_isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
