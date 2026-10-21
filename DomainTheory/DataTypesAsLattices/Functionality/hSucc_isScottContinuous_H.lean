/-ai
For fixed e and t, the map sending H to the successor clause hSucc H e t is Scott continuous.

The ternary continuity theorem applies to the three continuity lemmas for the conditional set. The test is the composite of application of the tag combinator with application of H, continuous in H. The zero branch is the composite of the left injection, the successor, and the untagged-payload combinator around the same application of H. The positive branch is the constant bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hSucc_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hSucc H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (funOf_isScottContinuous whichC) (hApply_isScottContinuous_H _ t))
    (theorem_1_3 (funOf_isScottContinuous inleftC)
      (theorem_1_3 succSet_isScottContinuous
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))))
    (const_isScottContinuous botElem)

end DomainTheory.DataTypesAsLattices
