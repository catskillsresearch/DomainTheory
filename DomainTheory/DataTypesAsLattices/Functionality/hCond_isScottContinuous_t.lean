/-ai
For a fixed candidate and code, the conditional clause is Scott-continuous in the environment.

The proof is Theorem 1.3 of continuity of application of the lambda retract with the ternary continuity package of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of application of the candidate at the zeroth payload component. The middle argument is an inner ternary package whose test is Theorem 1.3 of continuity of application of elimination with that same continuity, and whose branches are continuity of application at the first and second payload components. The outer third argument is continuity of application at the third payload component.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hCond_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun t =>
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
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous whichC)
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf_isScottContinuous outC)
          (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 2)))))
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 3)))))

end DomainTheory.DataTypesAsLattices
