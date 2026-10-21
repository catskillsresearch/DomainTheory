/-ai
For a fixed subexpression and environment, the recursive call is Scott-continuous in the candidate.

The proof is Theorem 1.3 of left continuity of application at the environment and left continuity of application at the subexpression.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hApply_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := fun H => funOf H e)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous_left e)

end DomainTheory.DataTypesAsLattices
