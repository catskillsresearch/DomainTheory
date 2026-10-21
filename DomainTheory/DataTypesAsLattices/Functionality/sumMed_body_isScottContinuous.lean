/-ai
The conditional body of the coproduct mediator, reading the tag of u and applying f or g to the payload, is Scott continuous.

The continuity theorem for an operation of three arguments is applied to the three continuity lemmas for the conditional, to left continuity of application at the numeral 0, and to the two payload branches. Each branch is Theorem 1.3 applied to application of f, or of g, and to left application at the numeral 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_body_isScottContinuous (f g : Pomega) :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1)))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (funOf_isScottContinuous f)
      (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous g)
      (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
