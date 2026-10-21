/-ai
For a fixed candidate, environment, and index, the recursive call on the application of the payload to that numeral is Scott-continuous in the code.

The proof is Theorem 1.3 of continuity of the recursive call in the subexpression and of Theorem 1.3 of left continuity of application at the index with left continuity of the payload, which is application at the numeral 1.
ai-/
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
