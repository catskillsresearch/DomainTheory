module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion_isScottContinuous_t

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hLam_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun t =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))
    (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun t x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        theorem_1_3
          (f := funOf (funOf H (funOf (expPayload e) (ofNat 1))))
          (g := fun t => updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))
          (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
          (updateEnvUnion_isScottContinuous_t x
            (funOf (expPayload e) (ofNat 0)))))

end DomainTheory.DataTypesAsLattices
