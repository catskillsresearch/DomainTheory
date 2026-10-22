module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hApply_payload_isScottContinuous_e (H t : Pomega) (i : ℕ) :
    IsScottContinuous (fun e =>
      hApply H (funOf (expPayload e) (ofNat i)) t) :=
  theorem_1_3 (f := fun e => hApply H e t)
    (g := fun e => funOf (expPayload e) (ofNat i))
    (hApply_isScottContinuous_e H t)
    (theorem_1_3 (f := fun u => funOf u (ofNat i)) (g := expPayload)
      (funOf_isScottContinuous_left (ofNat i))
      (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
