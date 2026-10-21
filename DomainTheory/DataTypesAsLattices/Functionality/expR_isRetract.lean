/-ai
Scott 1976, Theorem 4.6 applied to (4.44). The expression retract is a retract.

This is the second component of Theorem 4.6 applied to Scott continuity of the syntax functor. The functor preserves retracts by the seven-fold sum of retracts, using that the integer retract and bottom are retracts, the four-fold tensor of the argument, the binary tensor of the argument, and the tensor of the integer retract with the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.expF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.6 applied to (4.44).** -/
theorem expR_isRetract : IsRetract expR :=
  (theorem_4_6 expF_isScottContinuous (fun _a ha =>
    plus7_isRetract intR_isRetract bot_isRetract ha ha
      (tensor4_isRetract ha ha ha ha) (tensorR_isRetract ha ha)
      (tensorR_isRetract intR_isRetract ha))).2

end DomainTheory.DataTypesAsLattices
