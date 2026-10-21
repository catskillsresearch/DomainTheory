/-ai
For fixed H and e, the map sending an environment t to the predecessor clause hPred H e t is Scott continuous.

The ternary continuity theorem applies to the three continuity lemmas for the conditional set. The test is application of the tag combinator composed with application of the constant value of H at the payload of e, which is Scott continuous in t. The zero branch is the left injection of the predecessor of the untagged payload of that same application. The positive branch is the constant bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hPred_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hPred H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun t => hApply H (expPayload e) t)
      (funOf_isScottContinuous whichC)
      (funOf_isScottContinuous (funOf H (expPayload e))))
    (theorem_1_3 (f := funOf inleftC)
      (g := fun t => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf_isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun t => funOf outC (hApply H (expPayload e) t))
        predSet_isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun t => hApply H (expPayload e) t)
          (funOf_isScottContinuous outC)
          (funOf_isScottContinuous (funOf H (expPayload e))))))
    (const_isScottContinuous botElem)

end DomainTheory.DataTypesAsLattices
