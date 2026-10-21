/-ai
The interpreter step at a tag-zero injection of x, on an environment, equals the application of that environment to x.

Unfold the step, the expression tag and payload, and the variable clause. The tag of a zero injection is the numeral zero, so the definite conditional selects its first branch, and the payload of the injection is x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag0 (H x t : Pomega) :
    Hstep H (tagInj 0 x) t = funOf t x := by
  simp only [Hstep, expTag, expPayload, hVar, tagInj_zero, tagInj_one,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
