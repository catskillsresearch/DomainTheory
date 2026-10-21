/-ai
For a fixed candidate and environment, the application clause is Scott-continuous in the code.

The ternary continuity package uses the three separate continuities of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of the recursive call in the code through the payload at index 0. The middle argument is the constant bottom. The third argument is the binary continuity package of left continuity of application and continuity of application, fed by Theorem 1.3 of continuity of application of elimination with that same payload continuity at index 0, and by the payload continuity at index 1.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_payload_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hApp_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf_isScottContinuous whichC)
      (hApply_payload_isScottContinuous_e H t 0))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous outC)
        (hApply_payload_isScottContinuous_e H t 0))
      (hApply_payload_isScottContinuous_e H t 1))

end DomainTheory.DataTypesAsLattices
