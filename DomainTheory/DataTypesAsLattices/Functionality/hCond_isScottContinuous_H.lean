/-ai
For a fixed code and environment, the conditional clause is Scott-continuous in the candidate.

The proof is Theorem 1.3 of continuity of application of the lambda retract with the ternary continuity package of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of the recursive call in the candidate. The middle argument is an inner ternary package whose test is Theorem 1.3 of continuity of application of elimination and continuity of the recursive call, and whose two branches are that same continuity. The outer third argument is again continuity of the recursive call in the candidate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hCond_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hCond H e t) :=
  theorem_1_3 (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC)
        (hApply_isScottContinuous_H _ t))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))
        (hApply_isScottContinuous_H _ t)
        (hApply_isScottContinuous_H _ t))
      (hApply_isScottContinuous_H _ t))

end DomainTheory.DataTypesAsLattices
