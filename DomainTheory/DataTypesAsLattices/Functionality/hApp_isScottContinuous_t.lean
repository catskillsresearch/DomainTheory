/-ai
For a fixed candidate and code, the application clause is Scott-continuous in the environment.

The ternary continuity package uses the three separate continuities of the conditional. The test is Theorem 1.3 of continuity of application of the which combinator and continuity of application of the candidate at the zeroth payload component. The middle argument is the constant bottom. The third argument is the binary continuity package of left continuity of application and continuity of application, fed by Theorem 1.3 of continuity of application of elimination with continuity of application at the zeroth payload component, and by continuity of application at the first payload component.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hApp_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf_isScottContinuous whichC)
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous outC)
        (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
