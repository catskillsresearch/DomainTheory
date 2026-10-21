/-ai
For fixed H and t, the map sending e to the predecessor clause hPred H e t is Scott continuous.

The value of H at the payload of e is the composite of application of H in the expression argument with the payload projection. The ternary continuity theorem applies to the three continuity lemmas for the conditional set. The test is application of the tag combinator composed with that value, the zero branch is the left injection of the predecessor of the untagged payload of that value, and the positive branch is the constant bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hPred_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hPred H e t) :=
  let hrec :=
    theorem_1_3 (f := fun e => hApply H e t) (g := expPayload)
      (hApply_isScottContinuous_e H t)
      (funOf_isScottContinuous_left (ofNat 1))
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun e => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC) hrec)
    (theorem_1_3 (f := funOf inleftC)
      (g := fun e => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun e => funOf outC (hApply H (expPayload e) t))
        predSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun e => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC) hrec)))
    (const_isScottContinuous botElem)

end DomainTheory.DataTypesAsLattices
