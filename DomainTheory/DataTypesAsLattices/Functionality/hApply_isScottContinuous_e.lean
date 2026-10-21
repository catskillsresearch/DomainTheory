/-ai
For a fixed candidate and environment, the recursive call is Scott-continuous in the subexpression.

The proof is Theorem 1.3 of left continuity of application at the environment and continuity of application of the candidate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hApply_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := funOf H)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous H)

end DomainTheory.DataTypesAsLattices
