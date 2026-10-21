/-ai
For fixed H and e, the map sending an environment t to the abstraction clause hLam H e t is Scott continuous.

Composition applies the right injection, which is Scott continuous, to the graph of the map that evaluates H at the second component of the payload of e, in the environment updated by the bound value at the first component of that payload. That graph is continuous in t because its body is the composite of the constant application of H at that second component with the environment update, and the update is Scott continuous in t.
ai-/

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
