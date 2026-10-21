/-ai
For a fixed candidate and environment, the conditional clause is Scott-continuous in the code.

The proof is Theorem 1.3 of continuity of application of the lambda retract with the ternary continuity package of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of the recursive call in the code through the payload at index 0. The middle argument is an inner ternary package whose test is Theorem 1.3 of continuity of application of elimination with that same payload continuity, and whose branches are the payload continuities at indices 1 and 2. The outer third argument is the payload continuity at index 3.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_payload_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hCond_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun e =>
      condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
          (hApply H (funOf (expPayload e) (ofNat 1)) t)
          (hApply H (funOf (expPayload e) (ofNat 2)) t))
        (hApply H (funOf (expPayload e) (ofNat 3)) t))
    (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous whichC)
        (hApply_payload_isScottContinuous_e H t 0))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf_isScottContinuous outC)
          (hApply_payload_isScottContinuous_e H t 0))
        (hApply_payload_isScottContinuous_e H t 1)
        (hApply_payload_isScottContinuous_e H t 2))
      (hApply_payload_isScottContinuous_e H t 3))

end DomainTheory.DataTypesAsLattices
