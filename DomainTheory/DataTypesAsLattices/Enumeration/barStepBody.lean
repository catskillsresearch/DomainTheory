module

public import DomainTheory.DataTypesAsLattices.Enumeration.barPos
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Graph.funOf_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.15).** Step of `ū = λx. x₀ ⊃ ⟨1, u, x₁⟩, overline{u(x₁)(x₂)}`. -/
def barStepBody (B u x : Pomega) : Pomega :=
  condSet (funOf x (ofNat 0)) (barPos u x)
    (funOf (funOf B (funOf u (funOf x (ofNat 1)))) (funOf x (ofNat 2)))

namespace barStepBody

theorem isScottContinuous_B (u x : Pomega) :
    IsScottContinuous (fun B => barStepBody B u x) :=
  theorem_1_3 (condSet.isScottContinuous_right (funOf x (ofNat 0)) (barPos u x))
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun B => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (funOf_isScottContinuous_left (funOf u (funOf x (ofNat 1)))))

theorem isScottContinuous_u (B x : Pomega) :
    IsScottContinuous (fun u => barStepBody B u x) :=
  theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_mid (funOf x (ofNat 0)) y)
    (fun w => condSet.isScottContinuous_right (funOf x (ofNat 0)) w)
    (barPos.isScottContinuous_u x)
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun u => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (theorem_1_3 (funOf_isScottContinuous B)
        (funOf_isScottContinuous_left (funOf x (ofNat 1)))))

theorem isScottContinuous_x (B u : Pomega) :
    IsScottContinuous (fun x => barStepBody B u x) :=
  theorem_1_3.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun tes z => condSet.isScottContinuous_mid tes z)
    (fun tes th => condSet.isScottContinuous_right tes th)
    (funOf_isScottContinuous_left (ofNat 0))
    (barPos.isScottContinuous_x u)
    (theorem_1_3.tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun w => funOf_isScottContinuous w)
      (theorem_1_3 (funOf_isScottContinuous B)
        (theorem_1_3 (funOf_isScottContinuous u)
          (funOf_isScottContinuous_left (ofNat 1))))
      (funOf_isScottContinuous_left (ofNat 2)))

end barStepBody

end DomainTheory.DataTypesAsLattices
