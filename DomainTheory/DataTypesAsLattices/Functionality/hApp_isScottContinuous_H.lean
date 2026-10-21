/-ai
For a fixed code and environment, the application clause is Scott-continuous in the candidate interpretation.

The ternary continuity package uses the three separate continuities of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of the recursive call in the candidate. The middle argument is the constant bottom. The third argument is the binary continuity package of left continuity of application and continuity of application, fed by Theorem 1.3 of continuity of application of elimination with continuity of the recursive call in the candidate, and by that same continuity of the recursive call.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem hApp_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (funOf_isScottContinuous whichC)
      (hApply_isScottContinuous_H _ t))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (funOf_isScottContinuous outC)
        (hApply_isScottContinuous_H _ t))
      (hApply_isScottContinuous_H _ t))

end DomainTheory.DataTypesAsLattices
