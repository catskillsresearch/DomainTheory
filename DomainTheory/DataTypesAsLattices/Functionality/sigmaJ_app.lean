
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_app (j : ℕ) (x : Pomega) :
    funOf (graph (sigmaJ j)) x = sigmaJ j x := by
  simpa using congrArg (fun g => g x) (theorem_1_2_i (sigmaJ_isScottContinuous j))

end DomainTheory.DataTypesAsLattices
