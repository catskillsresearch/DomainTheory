/-ai
Scott 1976, (4.38). The tree retract equals the sum of bottom with the tensor of the tree retract with itself.

Theorem 2.5, from Scott continuity of the tree functor, identifies the tree retract with the fixed point of that functor. Theorem 1.4 says the fixed point is fixed, so the functor returns the tree retract. The reverse of that equality is the claim.
ai-/
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
