/-ai
The interpreter step at a tag-one injection equals the zero clause.

Unfold the step and the expression tag. The tag is the numeral one, so the outer definite conditional takes its second branch. The predecessor of one is zero, so the next definite conditional takes its first branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
