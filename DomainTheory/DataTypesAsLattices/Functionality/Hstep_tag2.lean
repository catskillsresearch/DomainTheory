/-ai
The interpreter step at a tag-two injection of an element equals the successor clause at that same tagged expression.

Unfold the step and the expression tag. The tag is the numeral two. Each definite conditional at a positive numeral takes its second branch, and predecessor lowers the numeral by one, until the conditional at zero selects the successor clause.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_tag2 (H x t : Pomega) :
    Hstep H (tagInj 2 x) t = hSucc H (tagInj 2 x) t := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_succ, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
