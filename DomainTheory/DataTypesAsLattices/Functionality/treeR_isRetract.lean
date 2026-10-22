/-ai
Scott's Theorem 4.6, applied to equation (4.38), states that the tree retract is a retract.

The second component of Theorem 4.6 is applied to the Scott continuity of the tree functional, using that the sum of the bottom retract with the tensor product of a retract with itself is a retract.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.treeF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.6 applied to (4.38).** -/
theorem treeR_isRetract : Retract treeR :=
  (theorem_4_6 treeF_isScottContinuous (fun _a ha =>
    plusR_isRetract bot_isRetract (tensorR_isRetract ha ha))).2

end DomainTheory.DataTypesAsLattices
