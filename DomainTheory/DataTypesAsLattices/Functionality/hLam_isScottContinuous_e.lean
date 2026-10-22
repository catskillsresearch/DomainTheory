module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion_isScottContinuous_idx

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hLam_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun e =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))
    (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun e x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        continuous_tuple
          (fun y =>
            theorem_1_3 (f := fun u => funOf u y) (g := funOf H)
              (funOf_isScottContinuous_left y) (funOf_isScottContinuous H))
          (fun u => funOf_isScottContinuous (funOf H u))
          (theorem_1_3 (f := fun u => funOf u (ofNat 1)) (g := expPayload)
            (funOf_isScottContinuous_left (ofNat 1))
            (funOf_isScottContinuous_left (ofNat 1)))
          (theorem_1_3 (f := updateEnvUnion t x)
            (g := fun e => funOf (expPayload e) (ofNat 0))
            (updateEnvUnion_isScottContinuous_idx t x)
            (theorem_1_3 (f := fun u => funOf u (ofNat 0)) (g := expPayload)
              (funOf_isScottContinuous_left (ofNat 0))
              (funOf_isScottContinuous_left (ofNat 1))))))

end DomainTheory.DataTypesAsLattices
